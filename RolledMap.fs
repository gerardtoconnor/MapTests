module RolledMap

// type NodeType =
// | MatchesValueEdges
// | MatchesEdges
// | MatchesValue
// | Edges
// | Value
// | Removed

let nMatch   = 0b1000uy
let nValue   = 0b0100uy
let nEdges   = 0b0010uy
let nRemoved = 0b0001uy

let inline ( &? )  nodeType pattern = (nodeType &&& pattern) <> 0uy  

(* NODE STRUCTURE
0-Node type
    byte1 - flag to identify field layout 
1-char matching
    byte1       : number chars to match
    [byte2 - n] : char(s) match
2-value
    byte1-byte4 : depending on # items, number of bytes for value index byte/int16/in32
3-edges
    byte1     : number of edges
    [
        (byte1,      : char to match
        byte2-byte3) : int16/int32
    ]
*)

type NodeType =
| MatchesValueEdges = 0 // m#,1..n,v1..vn,
| MatchesEdges      = 1
| MatchesValue      = 2
| Edges             = 3
| Value             = 4
| Removed           = 5

let inline bucketIndex (index:int) = index >>> 8
let inline shardIndex (index:int) = index &&& 0b11111111

let inline int2 (pos:node:byte []) = struct (pos + 2, ((int node.[pos]) <<< 8) &&& (int node.[pos + 1]) )

type RolledMap<'T>(items : (string * 'T) seq) =
    let bucket = Array.zeroCreate<byte []>(2)
    let values = Array.zeroCreate<'T>(2)

    let readMatches(mp,kp,key:string,node:byte []) =
        let mcount = int node.[0]
        let rec go mov =
            let nmp = mp + mov
            let nkp = kp + mov
            if node.[mp] = byte key.[nkp] then
                if mov < mcount then
                    go (mov + 1)
                else
                    mov
            else
                -1
        go 1 // skip count header

    let readValue(mp,node:byte []) = 
        let vi = ((int node.[mp]) <<< 8) &&& (int node.[mp + 1]) 
        Some values.[vi]

    let readEdges(mp,kp,key:string,node:byte []) =
        let ecount = int node.[mp]
        let mp = mp + 1 //mode to first node

        let c = key.[kp]
        Char 

        let rec go(l,r) = 
            if l > r then 
                None 
            else
                let m = (l + r) / 2
                if edges.[m].Char = v then edges.[m].Node |> Some
                else if edges.[m].Char < v then go (m + 1, r)
                else if edges.[m].Char > v then go (l ,m - 1)
                else None
                match edges.Count with 
                | 0 -> None
                | 1 -> if edges.[0].Char = v then edges.[0].Node |> Some else None 
                | n -> go(0 , n - 1)

        





/// testing
let v = 1798482

let intAry = [|v|]

let b1 = byte (v >>> 24 &&& 0b11111111 )
let b2 = byte (v >>> 16 &&& 0b11111111 )
let b3 = byte (v >>>  8 &&& 0b11111111 )
let b4 = byte (v        &&& 0b11111111 )

let byteAry = [|b1;b2;b3;b4|]
//#time
for _ in 0 .. 100000000 do
    let same = ( (int byteAry.[0]) <<< 24) ||| ( (int byteAry.[1]) <<< 16) ||| ( (int byteAry.[2]) <<< 8) ||| ( (int byteAry.[3]) ) = 1798482
    ()

for _ in 0 .. 100000000 do
    let same = System.BitConverter.ToInt32(byteAry,0) = 1798482
    ()

    let rec readNode (mp:int,kp:int,key:string) =
        let ntype = bucket.[bucketIndex index].[shardIndex index]
         
        let mutable mp = mp 
            
        if ntype &? nMatch then 
            mp <- readMatches(mp + 1,kp,key)

        if mp <> - 1 then
            
            if ntype &? nValue then
                readValue()
            
            if ntype &? nEdges then





for _ in 0 .. 100000000 do
    let same = intAry.[0] = 1798482
    ()

for _ in 0 .. 100000000 do
    let same = v = 1798482
    ()


let bsprint (value:int) =  System.Convert.ToString(value, 2).PadLeft(32, '0')

bsprint v
bsprint (int b1)
bsprint (int b2)
bsprint (int b3)
bsprint (int b4)

bsprint ( (int b1) <<< 24)

let v2 = ( (int b2) <<< 16) ||| ( (int b3) <<< 8) ||| ( (int b4) )

///

open System.IO
open System.Collections.Generic
let chars = System.Collections.Generic.Dictionary<char,int64>(100)
let [<Literal>] path = @"F:\Code\visualfsharp-original"

for fi in Directory.EnumerateFiles(path,"*.fs?",SearchOption.AllDirectories) do
    printfn "> checking: %s" fi
    for line in System.IO.File.ReadLines(fi) do
        for c in line do
            if chars.ContainsKey c then
                chars.[c] <- chars.[c] + 1L
            else
                chars.Add(c,1L)

printfn "> %i unique chars found"
let mutable maxchar = 0uy
for kvp in chars do
    let b = byte (kvp.Key)
    maxchar <- max b maxchar
    printfn "- %A [%A]: %i" kvp.Key (byte kvp.Key) kvp.Value
printfn "> MAX Char: %i" maxchar
printfn "%i" chars.Count