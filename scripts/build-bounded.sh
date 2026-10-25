#!/usr/bin/env bash
set -euo pipefail

# Limit concurrent compiler processes. The unmodified pinned Lean executable
# performs every compilation; this changes no proof or kernel option.
cd "$(dirname "$0")/.."
command -v flock >/dev/null
prefix=$(lean --print-prefix)
mirror="$PWD/.lake/build-toolchain"
mkdir -p "$mirror/bin" "$PWD/.lake/compiler-slots"
for item in "$prefix"/*; do
  name=$(basename "$item")
  if [ "$name" != bin ]; then
    ln -sfn "$item" "$mirror/$name"
  fi
done
for item in "$prefix/bin"/*; do
  name=$(basename "$item")
  if [ "$name" != lean ]; then
    ln -sfn "$item" "$mirror/bin/$name"
  fi
done
cat > "$mirror/bin/lean" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
compile=false
for argument in "$@"; do
  if [[ "$argument" == *.lean ]]; then compile=true; fi
done
if ! "$compile"; then exec "$EULER_REAL_LEAN" "$@"; fi
export LEAN_NUM_THREADS=${EULER_LEAN_THREADS:-1}
slots=${EULER_COMPILE_SLOTS:-1}
if ! [[ "$slots" =~ ^[1-9][0-9]*$ ]]; then
  echo "EULER_COMPILE_SLOTS must be a positive integer" >&2
  exit 1
fi
while :; do
  for ((slot = 0; slot < slots; slot++)); do
    exec 9>"$EULER_COMPILER_LOCKS/slot-$slot"
    if flock --nonblock 9; then
      "$EULER_REAL_LEAN" "$@"
      exit $?
    fi
    exec 9>&-
  done
  sleep 0.2
done
WRAPPER
chmod +x "$mirror/bin/lean"
export EULER_REAL_LEAN="$prefix/bin/lean"
export EULER_COMPILER_LOCKS="$PWD/.lake/compiler-slots"
export EULER_COMPILE_SLOTS=${EULER_COMPILE_SLOTS:-1}
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
export LAKE_OVERRIDE_LEAN=true
export LEAN_SYSROOT="$mirror"
if [ "$#" -gt 0 ]; then
  LEAN_NUM_THREADS=${EULER_LAKE_THREADS:-4} "$prefix/bin/lake" build "$@"
else
  LEAN_NUM_THREADS=${EULER_LAKE_THREADS:-4} "$prefix/bin/lake" build
fi
