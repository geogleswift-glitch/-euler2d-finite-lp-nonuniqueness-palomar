#!/usr/bin/env python3
"""Source-only release preflight; Python 3.10+, standard library only.

Run: python scripts/check_sources.py
The scan includes unused and untracked files, excluding only .git and .lake.
It does not replace Lean compilation, transitive axiom audits, Comparator, or
independent kernel replay. The lexer handles comments and literal strings;
it is not a Lean parser or an audit of arbitrary metaprogram execution.
Absolute private paths are checked in raw text, including comments and strings.
Direct filesystem operations and debugging writes are rejected in Lean code.

Policy: https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import stat
import sys

EXCLUDED = {".git", ".lake"}
ARTIFACT_SUFFIXES = {
    ".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj",
    ".so", ".ir", ".trace", ".exe", ".pyc", ".pyo",
}
TEX_SUFFIXES = {".tex", ".ltx", ".sty", ".cls"}
TEXT_SUFFIXES = {".lean", ".md", ".py", ".sh", ".json", ".toml", ".yaml", ".yml", ".txt"}
TEXT_NAMES = {"LICENSE", "lean-toolchain", ".gitignore", ".gitattributes"}
PRIVATE_PATH = re.compile(
    r"(?<![\w.])[A-Za-z]:[\\/]"
    r"|(?<![\w.])/(?:home|Users)/[^/\s\"']+"
    r"|(?<![\w.])/(?:root)(?=[/\\\s\"'`]|$)"
)
PROOF_IO = re.compile(
    r"(?<![\w'])(?:IO\.FS|FS\.[A-Za-z_][A-Za-z_0-9']*|"
    r"IO\.(?:eprintln|eprint|println|print))(?![\w'])"
)
FORBIDDEN = re.compile(
    r"(?<![\w'])(admit|axiom|unsafe|native_decide|sorryAx|ofReduceBool|"
    r"implemented_by|extern|allowUnsafeReducibility)(?![\w'])"
)
SORRY = re.compile(r"(?<![\w'])sorry(?![\w'])")
IDENTIFIER = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
THEOREM = re.compile(r"\b(?:theorem|lemma)\s+(" + IDENTIFIER + r")")
IMPORT = re.compile(r"(?m)^[ \t]*(?:public[ \t]+)?import[ \t]+([^\r\n]+)")
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
MAIN_RESULT = "PalomarEuler.main_result"


def physical_lines(data: bytes) -> int:
    """LF and CRLF delimit lines; a final newline adds no empty line."""
    return data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))


def inspect_private_paths(relative: str, source: str) -> list[str]:
    """Unlike the proof-token scan, this must also inspect literal strings."""
    return [
        f"{relative}:{source.count(chr(10), 0, item.start()) + 1}: private absolute filesystem path"
        for item in PRIVATE_PATH.finditer(source)
    ]


def mask_lean(source: str) -> tuple[str, list[int]]:
    """Blank nested comments/strings while preserving offsets and newlines."""
    result = list(source)
    documentation = []
    position = 0

    def blank(start: int, end: int) -> None:
        result[start:end] = ["\n" if c == "\n" else " " for c in source[start:end]]

    while position < len(source):
        start = position
        if source.startswith("--", position):
            end = source.find("\n", position)
            position = len(source) if end < 0 else end
            blank(start, position)
        elif source.startswith("/-", position):
            if source.startswith(("/-!", "/--"), position):
                documentation.append(position)
            depth = 1
            position += 2
            while position < len(source) and depth:
                if source.startswith("/-", position):
                    depth += 1
                    position += 2
                elif source.startswith("-/", position):
                    depth -= 1
                    position += 2
                else:
                    position += 1
            if depth:
                raise ValueError("unterminated block comment")
            blank(start, position)
        else:
            raw = None
            if source[position] == "r" and (
                position == 0 or not (source[position - 1].isalnum() or source[position - 1] == "_")
            ):
                raw = re.match(r'r(#{0,})"', source[position:])
            if raw:
                end_marker = '"' + raw.group(1)
                end = source.find(end_marker, position + raw.end())
                if end < 0:
                    raise ValueError("unterminated raw string")
                position = end + len(end_marker)
                blank(start, position)
            elif source[position] == '"':
                position += 1
                while position < len(source):
                    if source[position] == "\\":
                        position += 2
                    elif source[position] == '"':
                        position += 1
                        break
                    else:
                        position += 1
                else:
                    raise ValueError("unterminated string")
                blank(start, position)
            else:
                position += 1
    return "".join(result), documentation


def qualified_theorem_name(code: str, match: re.Match[str]) -> str:
    """Resolve the simple namespace/section layout used by this Challenge."""
    name = match.group(1)
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    stack: list[tuple[str, str]] = []
    command = re.compile(
        r"(?m)^[ \t]*(?:(?:@\[[^\r\n]*\]|noncomputable|public|private|protected)[ \t]+)*"
        r"(namespace|section|end)(?:[ \t]+(" + IDENTIFIER + r"))?[ \t]*$"
    )
    for item in command.finditer(code, 0, match.start()):
        kind, label = item.group(1), item.group(2) or ""
        if kind in {"namespace", "section"}:
            stack.append((kind, label))
        elif stack:
            stack.pop()
    prefix = ".".join(label for kind, label in stack if kind == "namespace")
    return prefix + "." + name if prefix else name


def inspect_challenge(code: str) -> list[str]:
    errors = []
    declarations = list(THEOREM.finditer(code))
    holes = list(SORRY.finditer(code))
    if len(declarations) != 1:
        errors.append("Challenge must contain exactly one theorem and no helper lemmas")
    elif qualified_theorem_name(code, declarations[0]) != MAIN_RESULT:
        errors.append("the sole Challenge theorem must be " + MAIN_RESULT)
    if len(holes) != 1:
        errors.append("Challenge must contain exactly one deliberate sorry")
    elif len(declarations) == 1:
        declaration, hole = declarations[0], holes[0]
        prefix = code[declaration.end():hole.start()]
        if hole.start() <= declaration.end() or not re.search(r":=\s*by\s*$", prefix):
            errors.append("the Challenge hole must be the complete final theorem proof ':= by sorry'")
        tail = code[hole.end():]
        if not re.fullmatch(r"\s*(?:end(?:[ \t]+" + IDENTIFIER + r")?\s*)*", tail):
            errors.append("only closing end commands may follow the Challenge theorem hole")
    for item in IMPORT.finditer(code):
        for imported in item.group(1).split():
            if imported.split(".")[0] not in {"Mathlib", "Init", "Lean", "Std"}:
                errors.append("Challenge imports a project/noncanonical module: " + imported)
    return errors


def source_files(root: Path, errors: list[str]):
    """Never follow submitted symlinks, junctions, or other reparse points."""
    def cannot_walk(error: OSError) -> None:
        errors.append("cannot traverse source directory: " + str(error))

    for directory, names, files in os.walk(root, followlinks=False, onerror=cannot_walk):
        names[:] = sorted(name for name in names if name not in EXCLUDED)
        for name in list(names) + sorted(files):
            if name in EXCLUDED:
                continue
            path = Path(directory) / name
            relative = path.relative_to(root).as_posix()
            try:
                info = path.lstat()
            except OSError as error:
                errors.append(f"{relative}: cannot inspect file: {error}")
                continue
            reparse = getattr(info, "st_file_attributes", 0) & getattr(
                stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400
            )
            if stat.S_ISLNK(info.st_mode) or reparse:
                errors.append(f"{relative}: submitted symlinks/reparse points are forbidden")
                if name in names:
                    names.remove(name)
            elif stat.S_ISREG(info.st_mode):
                yield path
            elif not stat.S_ISDIR(info.st_mode):
                errors.append(f"{relative}: submitted object is not a regular file/directory")


def load_config(root: Path, errors: list[str]) -> tuple[Path, str]:
    default = root / "Challenge.lean"
    try:
        config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        errors.append("comparator.json: " + str(error))
        return default, "Challenge"
    allowed = {
        "challenge_module", "solution_module", "theorem_names", "definition_names",
        "permitted_axioms", "enable_nanoda",
    }
    if not isinstance(config, dict):
        errors.append("comparator.json must be a JSON object")
        return default, "Challenge"
    if set(config) - allowed:
        errors.append("comparator.json contains unsupported fields: " + ", ".join(sorted(set(config) - allowed)))
    module = config.get("challenge_module")
    solution = config.get("solution_module")
    if not isinstance(module, str) or not re.fullmatch(IDENTIFIER, module):
        errors.append("comparator.json: invalid challenge_module")
        module = "Challenge"
    if not isinstance(solution, str) or not re.fullmatch(IDENTIFIER, solution):
        errors.append("comparator.json: invalid solution_module")
    elif not root.joinpath(*solution.split(".")).with_suffix(".lean").is_file():
        errors.append("comparator.json: Solution source is missing")
    if config.get("theorem_names") != [MAIN_RESULT]:
        errors.append("comparator.json: theorem_names must select only " + MAIN_RESULT)
    if config.get("definition_names", []) != []:
        errors.append("comparator.json: this Challenge permits no missing definition bodies")
    axioms = config.get("permitted_axioms")
    if not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms):
        errors.append("comparator.json: permitted_axioms must be a string list")
    elif len(axioms) != len(set(axioms)) or not set(axioms) <= PERMITTED_AXIOMS:
        errors.append("comparator.json: duplicate or forbidden permitted axioms")
    return root.joinpath(*module.split(".")).with_suffix(".lean"), module


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    errors: list[str] = []
    warnings: list[str] = []
    challenge, challenge_module = load_config(root, errors)
    lean_count = 0
    challenge_found = False
    largest = (0, "")
    for path in source_files(root, errors):
        relative = path.relative_to(root).as_posix()
        suffix = path.suffix.lower()
        if suffix in ARTIFACT_SUFFIXES or ".olean." in path.name.lower() or ".ilean." in path.name.lower():
            errors.append(f"{relative}: compiled/build artifacts are forbidden outside .lake")
        if any(part.lower() in TEX_SUFFIXES for part in path.suffixes):
            errors.append(f"{relative}: original TeX/material excluded by the release contract")
        if path.name == ".gitmodules":
            errors.append(f"{relative}: submitted Git submodules are forbidden")
        try:
            with path.open("rb") as handle:
                prefix = handle.read(200)
        except OSError as error:
            errors.append(f"{relative}: cannot read file: {error}")
            continue
        if prefix.startswith(b"version https://git-lfs.github.com/spec/v1"):
            errors.append(f"{relative}: Git LFS pointers are forbidden")
        if suffix in TEXT_SUFFIXES or path.name in TEXT_NAMES:
            try:
                raw_source = path.read_text(encoding="utf-8-sig")
            except (OSError, UnicodeError) as error:
                errors.append(f"{relative}: cannot read UTF-8 source text: {error}")
                continue
            errors.extend(inspect_private_paths(relative, raw_source))
        if suffix != ".lean":
            continue
        lean_count += 1
        data = path.read_bytes()
        lines = physical_lines(data)
        largest = max(largest, (lines, relative))
        if lines > 10000:
            errors.append(f"{relative}: {lines} physical lines exceeds 10000")
        try:
            code, documentation = mask_lean(data.decode("utf-8-sig"))
        except (UnicodeError, ValueError) as error:
            errors.append(f"{relative}: {error}")
            continue
        first_code = re.search(r"\S", code)
        if path.name != "lakefile.lean":
            if not re.match(r"\s*module[ \t]*(?:\r?\n|$)", code):
                errors.append(f"{relative}: missing module header before all code")
            elif first_code and any(position < first_code.start() for position in documentation):
                errors.append(f"{relative}: documentation comments must follow the module header")
        for item in FORBIDDEN.finditer(code):
            line = code.count("\n", 0, item.start()) + 1
            errors.append(f"{relative}:{line}: forbidden trust escape/proof placeholder: {item.group()}")
        for item in PROOF_IO.finditer(code):
            line = code.count("\n", 0, item.start()) + 1
            errors.append(f"{relative}:{line}: filesystem/debug I/O is forbidden in proof sources: {item.group()}")
        if re.search(r"\bset_option\s+debug\.skipKernelTC\s+true\b", code):
            errors.append(f"{relative}: disabling kernel type checking is forbidden")
        if re.search(r"\bdecide\s*\+\s*native\b", code):
            errors.append(f"{relative}: native decide is forbidden")
        if path == challenge:
            challenge_found = True
            if lines > 1000 or len(data) > 100 * 1024:
                errors.append(f"{relative}: Challenge exceeds 1000 lines or 100 KiB")
            elif lines > 300 or len(data) > 32 * 1024:
                warnings.append(f"{relative}: exceeds the 300-line/32-KiB Challenge warning threshold")
            errors.extend(f"{relative}: {error}" for error in inspect_challenge(code))
        else:
            for item in SORRY.finditer(code):
                line = code.count("\n", 0, item.start()) + 1
                errors.append(f"{relative}:{line}: sorry is forbidden in the proof development")
            for item in IMPORT.finditer(code):
                if challenge_module in item.group(1).split():
                    errors.append(f"{relative}: proof development must not import Challenge")
    if not challenge_found:
        errors.append("Challenge source is missing: " + challenge.relative_to(root).as_posix())
    if lean_count == 0:
        errors.append("no Lean source files found")
    for warning in warnings:
        print("WARNING:", warning)
    for error in errors:
        print("ERROR:", error, file=sys.stderr)
    print(f"Checked {lean_count} Lean files; largest: {largest[0]} lines ({largest[1]}).")
    if errors:
        print(f"Source preflight FAILED with {len(errors)} issue(s).", file=sys.stderr)
        return 1
    print("Source preflight passed; compilation and kernel verification are separate requirements.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
