﻿// Learn more about F# at http://fsharp.org

open System
open BenchmarkDotNet.Running
open ShardMap.Tests

[<EntryPoint>]
let main argv =
    printfn "Starting Banchmark tests"
    //BenchmarkRunner.Run<CreateNumberStringMaps>()
    //BenchmarkRunner.Run<LookupTests>();
    BenchmarkRunner.Run<ExistsTest>()
    //BenchmarkRunner.Run<SeqIttrTest>();
    //BenchmarkRunner.Run<AddNewTests>();
    //BenchmarkRunner.Run<MappingTests>();
    BenchmarkRunner.Run<FoldTests>()
    0 // return an integer exit code
