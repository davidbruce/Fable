@echo off

dotnet tool restore
dotnet run --project src/Fable.Build/Fable.Build.fsproj -- %*
