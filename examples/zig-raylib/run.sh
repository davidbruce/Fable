#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/../.." && pwd)"

export DOTNET_ROOT="${DOTNET_ROOT:-/Users/davidbruce/.local/share/mise/installs/dotnet/10.0.111}"
export PATH="/Users/davidbruce/.local/share/mise/installs/dotnet/10.0.111:/Users/davidbruce/.local/share/mise/installs/zig/0.17.1:/Users/davidbruce/.local/share/mise/installs/node/26.12.0/bin:$PATH"

cd "$DIR"

if ! grep -q "FABLE_COMPILER" "$DIR"/*.fs "$DIR"/Examples/*.fs; then
    echo "[check] Verified zero #if FABLE_COMPILER in examples/zig-raylib/*.fs"
else
    echo "[error] Found unexpected FABLE_COMPILER conditional in examples/zig-raylib"
    exit 1
fi

echo "[1/4] Running --verify on .NET 10..."
DOTNET_OUT=$(mktemp)
ZIG_DBG_OUT=$(mktemp)
ZIG_REL_OUT=$(mktemp)
trap 'rm -f "$DOTNET_OUT" "$ZIG_DBG_OUT" "$ZIG_REL_OUT"' EXIT

dotnet build -c Release "$DIR/RaylibExamples.fsproj" --disable-build-servers -m:1 >/dev/null
dotnet run --no-build -c Release --project "$DIR/RaylibExamples.fsproj" -- --verify > "$DOTNET_OUT"
cat "$DOTNET_OUT"

echo "[2/4] Transpiling to Zig & syncing fable-library-zig..."
if [ ! -d "$ROOT/temp/fable-library-zig" ]; then
    "$ROOT/build.sh" fable-library --zig
fi

dotnet "$ROOT/src/Fable.Cli/bin/Release/net10.0/fable.dll" \
    "$DIR/RaylibExamples.fsproj" \
    --lang zig \
    --extension .zig \
    --noCache

mkdir -p "$DIR/fable_modules/fable-library-zig"
cp -R "$ROOT/temp/fable-library-zig"/* "$DIR/fable_modules/fable-library-zig/"
cp "$ROOT/src/fable-library-zig"/*.zig "$DIR/fable_modules/fable-library-zig/"

echo "[3/4] Running Zig Debug --verify..."
zig build
"$DIR/zig-out/bin/raylib_examples" --verify > "$ZIG_DBG_OUT"

echo "[4/4] Running Zig ReleaseFast --verify..."
zig build -Doptimize=ReleaseFast
"$DIR/zig-out/bin/raylib_examples" --verify > "$ZIG_REL_OUT"

"$DIR/zig-out/bin/raylib_examples" --list >/dev/null

diff -u "$DOTNET_OUT" "$ZIG_DBG_OUT"
diff -u "$DOTNET_OUT" "$ZIG_REL_OUT"
echo "[PASS] .NET 10, Fable-Zig Debug, and Fable-Zig ReleaseFast outputs are byte-for-byte identical!"
