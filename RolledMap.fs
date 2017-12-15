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

let inline bucketIndex (index:int) = index >>> 8
let inline shardIndex (index:int) = index &&& 0b11111111

type RolledMap<'T>(items : (string * 'T) seq) =
    let bucket = Array.zeroCreate<byte []>(2)
    let values = Array.zeroCreate<'T []>(2)

    let readMatches(mp,kp,key:string) =
        let mcount = int bucket.[bucketIndex mp].[shardIndex mp]
        let rec go mov =
            let nmp = mp + mov
            let nkp = kp + mov
            if bucket.[bucketIndex nmp].[shardIndex nmp] = byte key.[nkp] then
                if mov < mcount then
                    go (mov + 1)
                else
                    mov
            else
                -1
        go 1 // skip count header

    let readValue(mp) = 
        let bi = bucketIndex mp
        let vi = bucket.[bi].[shardIndex mp]  
        values.[bucketIndex mp].[int vi]

    let readEdges( ) =

    let rec readNode (mp:int,kp:int,key:string) =
        let ntype = bucket.[bucketIndex index].[shardIndex index]
         
        let mp = 
            if ntype &? nMatch then 
                readMatches(mp + 1,kp,key)
            else
                mp

        if mp = - 1 then 
            - 1
        else

            let mp = 
                if ntype &? nValue then
                    readValue()





