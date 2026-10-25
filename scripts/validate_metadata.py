#!/usr/bin/env python3
"""Offline, project-specific formalization.yaml v0.4 release preflight.

Dependency: Python 3.10+ and PyYAML (python -m pip install PyYAML).
Run: python scripts/validate_metadata.py
Add --require-ready for the publication gate after all actual verification.
Optional: --schema /path/to/v0.4.schema.json also uses jsonschema
(python -m pip install jsonschema). Supply a reviewed, pinned, self-contained
upstream schema; this script never downloads one during validation.

This validates metadata shape and this project's release contract. It does
not prove factual provenance, theorem correctness, novelty, or a CI/kernel
verdict. Palomar's official intake and editorial checks remain required.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

AUTHORS = ["Tao Tao", "Haiqi Zhang"]
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
SOURCE_RELATIONSHIPS = {"formalizes", "adapts", "independently-proves", "background", "other"}
SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
METHODS = {"manual", "copilot", "agent", "autonomous", "other"}
ENDORSEMENTS = {"participated", "endorsed", "no-response", "not-contacted", "declined", "n/a", "other"}
LICENSE_NAME = re.compile(r"^(LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(\.(md|markdown|txt))?$", re.I)
# SHA-256 of whitespace-normalized canonical Apache-2.0 text, including appendix.
# Primary source: https://www.apache.org/licenses/LICENSE-2.0.txt
APACHE_2_SHA256 = "0ffddef9e48f8a09aed5caf2d44f7ba1c1be2d9b8e0a6f693b1635b2d5566645"
# The only subject codes selected for this project, checked against the primary
# PalomarSubmission taxonomy snapshot at c02bbeaed888df45c4e28c4e99dba540ad21552a.
ARXIV_CODES = {"math.AP"}
MSC_CODES = {"35Q31", "76B03"}


def load_metadata(path: Path) -> dict:
    try:
        import yaml
    except ImportError as error:
        raise ValueError("PyYAML is required; install it with: python -m pip install PyYAML") from error
    if path.is_symlink() or not path.is_file():
        raise ValueError("metadata must be a regular, non-symlink file")
    data = path.read_bytes()
    if len(data) > 256 * 1024:
        raise ValueError("metadata exceeds 256 KiB")

    class StrictLoader(yaml.SafeLoader):
        def compose_node(self, parent, index):
            if self.check_event(yaml.AliasEvent):
                raise yaml.constructor.ConstructorError(
                    None, None, "YAML aliases are excluded by this release preflight", self.peek_event().start_mark
                )
            return super().compose_node(parent, index)

        def construct_mapping(self, node, deep=False):
            result = {}
            for key_node, value_node in node.value:
                if key_node.tag == "tag:yaml.org,2002:merge":
                    raise yaml.constructor.ConstructorError(
                        None, None, "YAML merge keys are forbidden", key_node.start_mark
                    )
                key = self.construct_object(key_node, deep=deep)
                if not isinstance(key, str):
                    raise yaml.constructor.ConstructorError(
                        None, None, "mapping keys must be strings", key_node.start_mark
                    )
                if key in result:
                    raise yaml.constructor.ConstructorError(
                        None, None, "duplicate YAML key: " + key, key_node.start_mark
                    )
                result[key] = self.construct_object(value_node, deep=deep)
            return result

    try:
        value = yaml.load(data.decode("utf-8"), Loader=StrictLoader)
    except (UnicodeError, yaml.YAMLError) as error:
        raise ValueError(str(error)) from error
    if not isinstance(value, dict):
        raise ValueError("metadata must contain one top-level mapping")
    return value


def mapping(value, label: str, errors: list[str]) -> dict:
    if not isinstance(value, dict):
        errors.append(label + ": expected a mapping")
        return {}
    return value


def text(value, label: str, errors: list[str], maximum: int | None = None) -> bool:
    valid = isinstance(value, str) and bool(value.strip())
    if not valid:
        errors.append(label + ": expected a nonempty string")
    elif maximum is not None and len(value) > maximum:
        errors.append(f"{label}: exceeds {maximum} characters")
        valid = False
    return valid


def string_list(value, label: str, errors: list[str], minimum: int = 0, maximum: int | None = None) -> list:
    if not isinstance(value, list):
        errors.append(label + ": expected a list")
        return []
    if len(value) < minimum or (maximum is not None and len(value) > maximum):
        errors.append(label + ": wrong number of entries")
    for item in value:
        text(item, label + "[]", errors)
    if all(isinstance(item, str) for item in value) and len(value) != len(set(value)):
        errors.append(label + ": entries must be distinct")
    return value


def validate_license(root: Path, errors: list[str]) -> None:
    candidates = [path for path in root.iterdir() if LICENSE_NAME.fullmatch(path.name)]
    if len(candidates) != 1:
        errors.append("repository root must contain exactly one conventional license file")
        return
    path = candidates[0]
    if path.is_symlink() or not path.is_file():
        errors.append("license must be a regular, non-symlink file")
        return
    data = path.read_bytes()
    if not data or len(data) > 1024 * 1024:
        errors.append("license must be nonempty and at most 1 MiB")
        return
    try:
        normalized = re.sub(r"\s+", " ", data.decode("utf-8")).strip()
    except UnicodeError:
        errors.append("license must be UTF-8")
        return
    if hashlib.sha256(normalized.encode("utf-8")).hexdigest() != APACHE_2_SHA256:
        errors.append("license differs from the canonical Apache-2.0 text used by this release")


def validate(data: dict, root: Path, require_ready: bool = False) -> tuple[list[str], str]:
    errors: list[str] = []
    if data.get("version") != "v0.4":
        errors.append("version must be v0.4")
    project = mapping(data.get("project"), "project", errors)
    text(project.get("name"), "project.name", errors, 300)
    text(project.get("description"), "project.description", errors, 10000)
    for field in ("authors", "responsible_maintainers"):
        names = string_list(project.get(field), "project." + field, errors, minimum=1)
        if names != AUTHORS:
            errors.append("project." + field + " must list Tao Tao, then Haiqi Zhang")
    if project.get("license") != "Apache-2.0":
        errors.append("project.license must be Apache-2.0")
    if "repository" in data:
        errors.append("omit repository: this repository contains the substantive proof development")
    validate_license(root, errors)

    classification = mapping(data.get("classification"), "classification", errors)
    arxiv = string_list(classification.get("arxiv"), "classification.arxiv", errors, minimum=1, maximum=8)
    msc = string_list(classification.get("msc2020", []), "classification.msc2020", errors, maximum=8)
    if any(not isinstance(code, str) or code not in ARXIV_CODES for code in arxiv):
        errors.append("classification.arxiv must use this project's reviewed math.AP category")
    if any(not isinstance(code, str) or code not in MSC_CODES for code in msc):
        errors.append("classification.msc2020 contains a code outside this project's reviewed taxonomy")

    sources = data.get("sources")
    if not isinstance(sources, list) or not sources:
        errors.append("sources must be a nonempty list")
        sources = []
    relationships = []
    original = []
    for index, value in enumerate(sources):
        label = f"sources[{index}]"
        source = mapping(value, label, errors)
        text(source.get("title"), label + ".title", errors)
        relationship = source.get("relationship")
        relationships.append(relationship)
        if not isinstance(relationship, str) or relationship not in SOURCE_RELATIONSHIPS:
            errors.append(label + ": invalid relationship")
        kind = source.get("type")
        if "type" in source and (not isinstance(kind, str) or kind not in SOURCE_TYPES):
            errors.append(label + ": invalid source type")
        if kind == "original-proof":
            original.append(source)
            if relationship != "other":
                errors.append(label + ": original-proof requires relationship other")
        if relationship == "other":
            text(source.get("note"), label + ".note", errors)
        if "authors" in source:
            string_list(source["authors"], label + ".authors", errors)
        for field in ("id", "location", "note", "license"):
            if field in source:
                text(source[field], label + "." + field, errors)
        if "author_endorsement" in source and (
            not isinstance(source["author_endorsement"], str) or source["author_endorsement"] not in ENDORSEMENTS
        ):
            errors.append(label + ": invalid author_endorsement")
        contributors = source.get("contributors", [])
        if not isinstance(contributors, list):
            errors.append(label + ".contributors must be a list")
            contributors = []
        for contributor in contributors:
            person = mapping(contributor, label + ".contributors[]", errors)
            text(person.get("name"), label + ".contributors[].name", errors)
            text(person.get("role"), label + ".contributors[].role", errors, 200)
    origin = "original" if original else "source-based"
    if original:
        if any(
            not isinstance(relationship, str) or relationship not in {"background", "other"}
            for relationship in relationships
        ):
            errors.append("original-result metadata permits only background/other source relationships")
    elif not any(
        isinstance(relationship, str) and relationship in {"formalizes", "adapts", "independently-proves"}
        for relationship in relationships
    ):
        errors.append("source-based metadata needs a substantive formalizes/adapts/independently-proves source")
    if not original:
        errors.append("this release contract declares an original-proof source for the unpublished human result")
    if not any(source.get("authors") == AUTHORS for source in original):
        errors.append("the original-result source must credit the human authors in the requested order")
    if not any(
        isinstance(source, dict)
        and source.get("id") == "https://doi.org/10.4171/EMSS/34"
        and source.get("relationship") == "background"
        for source in sources
    ):
        errors.append("the Buckmaster--Vicol survey DOI must be cited separately as background")

    related = data.get("related_formalizations", [])
    if not isinstance(related, list):
        errors.append("related_formalizations must be a list")
        related = []
    for item in related:
        item = mapping(item, "related_formalizations[]", errors)
        text(item.get("id"), "related_formalizations[].id", errors)
        if not isinstance(item.get("relationship"), str) or item["relationship"] not in {
            "builds-on", "adapts", "independent", "supersedes", "other"
        }:
            errors.append("related_formalizations[]: invalid relationship")

    automation = mapping(data.get("automation"), "automation", errors)
    methods = automation.get("methods")
    if not isinstance(methods, list) or not methods:
        errors.append("automation.methods must be a nonempty list")
        methods = []
    for item in methods:
        item = mapping(item, "automation.methods[]", errors)
        if not isinstance(item.get("method"), str) or item["method"] not in METHODS:
            errors.append("automation.methods[].method must use a portable v0.4 category")
        if "models" in item:
            string_list(item["models"], "automation.methods[].models", errors)
        for field in ("framework", "tool_setup", "prompting_notes"):
            if field in item:
                text(item[field], "automation.methods[]." + field, errors)
    workflow = json.dumps(automation, ensure_ascii=False, default=str)
    for product in ("ChatGPT", "Aristotle", "Codex"):
        if product not in workflow:
            errors.append("automation must disclose the material role of " + product)

    status = mapping(data.get("status"), "status", errors)
    text(status.get("scope"), "status.scope", errors)
    for field in ("sorry_count", "sorry_in_definitions"):
        value = status.get(field)
        if type(value) is not int or value != 0:
            errors.append("status." + field + " must record integer zero for this release")
    axioms = string_list(status.get("axioms"), "status.axioms", errors)
    if any(not isinstance(axiom, str) or axiom not in PERMITTED_AXIOMS for axiom in axioms):
        errors.append("status.axioms contains a nonpermitted axiom")
    verification = status.get("verification")
    if not isinstance(verification, str) or verification not in {"pending", "complete"}:
        errors.append("status.verification must be pending or complete")
    if require_ready and verification != "complete":
        errors.append("release verification is pending; --require-ready requires actual completed verification")
    fidelity = mapping(data.get("fidelity"), "fidelity", errors)
    text(fidelity.get("divergences"), "fidelity.divergences", errors)
    review = mapping(data.get("review"), "review", errors)
    text(review.get("status"), "review.status", errors)
    text(review.get("notes"), "review.notes", errors)
    string_list(review.get("reviewers", []), "review.reviewers", errors)
    serialized = json.dumps(data, ensure_ascii=False, default=str)
    if re.search(r"\b(?:TEMPLATE|TODO|TBD|REPLACE_ME)\b", serialized):
        errors.append("metadata contains an unresolved template marker")
    return errors, origin


def validate_schema(data: dict, path: Path) -> list[str]:
    try:
        import jsonschema
    except ImportError:
        return ["--schema requires jsonschema; install it with: python -m pip install jsonschema"]
    try:
        schema = json.loads(path.read_text(encoding="utf-8"))
        # Do not permit hidden network requests or an unpinned dispatcher.
        serialized = json.dumps(schema)
        if re.search(r'"\$(?:dynamic)?ref"\s*:\s*"(?!#)', serialized, flags=re.I):
            return ["--schema must be a self-contained v0.4 schema without external references"]
        jsonschema.Draft7Validator.check_schema(schema)
        validator = jsonschema.Draft7Validator(schema)
        return [
            "upstream schema " + ".".join(map(str, issue.absolute_path)) + ": " + issue.message
            for issue in sorted(validator.iter_errors(data), key=lambda issue: str(issue.absolute_path))
        ]
    except (OSError, ValueError, jsonschema.SchemaError) as error:
        return ["cannot validate the supplied schema: " + str(error)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--metadata", type=Path, default=Path("formalization.yaml"))
    parser.add_argument("--schema", type=Path, help="optional pinned, self-contained v0.4 JSON schema")
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    path = args.metadata if args.metadata.is_absolute() else root / args.metadata
    try:
        data = load_metadata(path)
        errors, origin = validate(data, root, args.require_ready)
        if args.schema:
            errors.extend(validate_schema(data, args.schema))
    except (OSError, ValueError) as error:
        print("ERROR:", error, file=sys.stderr)
        return 2
    for error in errors:
        print("ERROR:", error, file=sys.stderr)
    if errors:
        print(f"Metadata preflight FAILED with {len(errors)} issue(s).", file=sys.stderr)
        return 1
    print(f"Metadata v0.4 preflight passed; declared result origin: {origin}.")
    print("Human authors and responsible maintainers: Tao Tao; Haiqi Zhang.")
    if data["status"]["verification"] != "complete":
        print("RELEASE PENDING: the structural metadata check is not a build or kernel verdict.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
