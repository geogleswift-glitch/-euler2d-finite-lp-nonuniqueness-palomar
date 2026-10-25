#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for command in bwrap lake lean python3; do
  command -v "$command" >/dev/null
done
prefix=$(lean --print-prefix)
for command in leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$command"
done
config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - "$prefix" "$config" <<'PY'
import json
import pathlib
import sys

prefix, destination = sys.argv[1:]
config = json.loads(pathlib.Path('comparator.json').read_text())
if 'external_kernels' in config:
    raise SystemExit('external_kernels is not a submitter-controlled field')
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [f'{prefix}/bin/nanoda_bin'],
    'con-ron': [f'{prefix}/bin/con-ron', '--jobs=2'],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY
# The resource gate is used only to prepare ordinary build artifacts. The
# sandboxed comparison itself uses the original, pinned toolchain binaries.
unset LAKE_OVERRIDE_LEAN LEAN_SYSROOT LEAN
"$prefix/bin/lake" comparator --config "$config"
