module ShardMap.Tests

open SampleData
open Internal.Utilities.Collections
open Xunit
open BenchmarkDotNet.Attributes
open System.Collections.Generic
open System
open BenchmarkDotNet.Running
open BenchmarkDotNet.Reports
open BenchmarkDotNet.Order
open Xunit.Abstractions


type CreateNumberStringMaps () =
    
    [<Benchmark(Baseline=true)>]
    member __.Create_ShardMap () =
        ShardMap<_,_>(numberStrings)

    [<Benchmark>]
    member __.Create_BMap () =
        Map<_,_>(numberStrings)

    [<Benchmark>]
    member __.Create_Dict () =
        let dict = Dictionary<_,_>(numberStrings.Length)
        for (k,v) in numberStrings do
            dict.Add(k,v)
        dict         

let getMaps () = 
    let mapgen =  CreateNumberStringMaps ()    
    mapgen.Create_ShardMap ()
    ,mapgen.Create_BMap ()
    ,mapgen.Create_Dict ()

type LookupTests() =

    let smap,bmap,dict = getMaps ()

    [<Fact>]
    [<Benchmark(Baseline=true)>]
    member __.ShardMap_contains_all_entries () = 
        for (k,v) in numberStrings do
            match smap.TryFind k with
            | Some r -> Assert.Equal(r,v)
            | None -> Assert.True(false)

    [<Fact>]
    [<Benchmark>]
    member __.ShardMap_contains_all_entries_TryGetValue () = 
        for (k,v) in numberStrings do
            let mutable result = Unchecked.defaultof<string>
            match smap.TryGetValue(k,&result) with
            | true  -> Assert.Equal(result,v)
            | false -> Assert.True(false)

    [<Fact>]
    [<Benchmark>]
    member __.ShardMap_contains_all_entries_FindOptStruct () = 
        for (k,v) in numberStrings do
            let opt = smap.TryFindOpt(k)
            match opt.Exists with
            | true  -> Assert.Equal(opt.Val,v)
            | false -> Assert.True(false)

    [<Benchmark>]
    member __.BMap_contains_all_entries () = 
        for (k,v) in numberStrings do
            match bmap.TryFind k with
            | Some r -> Assert.Equal(r,v)
            | None -> Assert.True(false)

    [<Benchmark>]
    member __.Dict_contains_all_entries () = 
        for (k,v) in numberStrings do
            match dict.TryGetValue k with
            | true, r -> Assert.Equal(r,v)
            | false,_ -> Assert.True(false)
        
type ExistsTest() =
    
    let smap,bmap,dict = getMaps ()
    
    [<Fact>]
    [<Benchmark>]
    member __.ShardMap_ExistsPar () = 
        Assert.True( smap.ExistsPar (fun _ v -> v = "3002087") )

    [<Fact>]
    [<Benchmark>]
    member __.ShardMap_Exists () = 
        Assert.True( smap.Exists (fun _ v -> v = "3002087") )
    
    [<Fact>]
    [<Benchmark>]
    member __.BMap_Exists () =
        Assert.True( Map.exists  (fun _ v -> v = "3002087") bmap )



type SeqIttrTest() = 
    let smap,bmap,dict = getMaps ()

    [<Fact>]
    [<Benchmark(Baseline=true)>]
    member __.ShardMap_SeqIttr () = 
        let mutable counter = 0 
        for item in smap do
            counter <- counter + 1
            let kvp = item
            ()
        Assert.Equal(numberStrings.Length ,counter)
    
    [<Benchmark>]
    member __.BMap_SeqIttr () =
        let mutable counter = 0 
        for item in bmap do
            counter <- counter + 1
            let kvp = item
            ()
        Assert.Equal(numberStrings.Length ,counter)

    [<Benchmark>]
    member __.Dict_SeqIttr () = 
        let mutable counter = 0 
        for item in dict do
            counter <- counter + 1
            let kvp = item
            ()
        Assert.Equal(numberStrings.Length ,counter)

type AddNewTests() =
    let smap,bmap,dict = getMaps ()
    
    [<Fact>]
    [<Benchmark(Baseline=true)>]
    member __.ShardMap_AddNew () = 
        let k,v = "Key1","Value1" 
        let ndict = smap.Add(k,v)
        Assert.True( ndict.ContainsKey(k) && not(smap.ContainsKey(k)) )
    
    [<Benchmark>]
    member __.Bmap_AddNew () = 
        let k,v = "Key1","Value1"
        let ndict = bmap.Add(k,v)
        Assert.True( ndict.ContainsKey(k) && not(bmap.ContainsKey(k)) )

    [<Benchmark>]
    member __.Dict_AddNew () = 
        let ndict = Dictionary<_,_>(dict)
        let k,v = "Key1","Value1" 
        ndict.Add(k,v)
        Assert.True( ndict.ContainsKey(k) && not(dict.ContainsKey(k)) )


type MappingTests() = 
    let smap,bmap,dict = getMaps ()

    [<Fact>]
    [<Benchmark(Baseline=true)>]
    member __.ShardMap_Map () = 
        smap.Map int |> ignore
        
    
    [<Benchmark>]
    member __.Bmap_Map () = 
        Map.map (fun _ v -> int v) bmap |> ignore

    [<Benchmark>]
    member __.Dict_Map () = 
        let ndict = Dictionary<string,int>(dict.Count)
        for item in dict do
            ndict.Add(item.Key,int item.Value)
        
type FoldTests() =
    let smap,bmap,dict = getMaps ()

    [<Fact>]
    [<Benchmark(Baseline=true)>]
    member __.ShardMap_Fold () = 
        smap.Fold (fun acc _ _ -> acc + 1) 0 |> ignore
    
    [<Benchmark>]
    member __.ShardMap_FoldReduce () =
        smap.FoldReduce (fun acc _ _ -> acc + 1) (+) 0 |> ignore
    
    [<Benchmark>]
    member __.BMap_Fold () =
        Map.fold (fun acc _ _ -> acc + 1 ) 0 bmap
    
