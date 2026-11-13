#!/bin/zsh
# Compile each benchmark to Zig (ReleaseFast) and to .NET (Release), check that both print the
# same, and time both (the best of three runs). Run `./build.sh quicktest zig` first: it
# compiles the runtime library into temp/fable-library-zig.
set -u
setopt null_glob
cd "$(dirname "$0")"
ROOT=$(cd ../.. && pwd)
DOTNET="${DOTNET:-dotnet}"
best() {
    local b=999999
    for _ in 1 2 3; do
        local s=$(date +%s%N 2>/dev/null || python3 -c 'import time; print(time.time_ns())')
        "$@" >/dev/null
        local e=$(date +%s%N 2>/dev/null || python3 -c 'import time; print(time.time_ns())')
        local ms=$(( (e - s) / 1000000 ))
        (( ms < b )) && b=$ms
    done
    echo $b
}
printf "%-10s %10s %10s  %s\n" benchmark "zig ms" ".NET ms" output
names=(${@:-nbody lists maps strings virtual})
[ $# -eq 0 ] && names=(nbody lists maps strings virtual)
for d in $names; do
    (cd $d
     rm -rf fable_modules; rm -f *.zig
     ${=DOTNET} run -c Release --no-build --project $ROOT/src/Fable.Cli -- . --lang zig --extension .zig --noCache --exclude Fable.Core >/dev/null 2>&1
     mkdir -p fable_modules && cp -r $ROOT/temp/fable-library-zig fable_modules/
     zig build-exe -O ReleaseFast Program.zig -femit-bin=bench-zig >/dev/null 2>&1 || { echo "$d: zig build failed"; exit 0; }
     ${=DOTNET} build -c Release -o bin/bench >/dev/null 2>&1
     z=$(./bench-zig); n=$(${=DOTNET} bin/bench/Bench.dll)
     [[ "$z" == "$n" ]] || echo "$d: outputs differ: zig [$z] .NET [$n]"
     printf "%-10s %10s %10s  %s\n" $d $(best ./bench-zig) $(best ${=DOTNET} bin/bench/Bench.dll) "$(echo $z | head -1)")
done
