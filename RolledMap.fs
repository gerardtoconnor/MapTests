module RolledMap

type NodeType =
| MatchesValueEdges
| MatchesEdges
| MatchesValue
| Edges
| Value
| Removed

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



