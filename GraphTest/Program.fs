open System
open System.Collections.Generic
open System.IO
open System.Threading

open Microsoft.FSharp.Control

open Shields.GraphViz.Models
open Shields.GraphViz.Components
open Shields.GraphViz.Services
open System.Numerics

//////////////////////////////////////////////////////////////////////////
// グラフ構築に必要な定義

// GraphVizを使用して、指定されたグラフを非同期で出力する
let renderAsync (imageFileName: string) (format: RendererFormats) (graph: Graph) = async {
    let programFolder = Environment.GetFolderPath(Environment.SpecialFolder.ProgramFilesX86)
    let rendererPath = Path.Combine(programFolder, "Graphviz2.38", "bin")
    let renderer = new Renderer(rendererPath)
    use file = File.Create(imageFileName)
    do! (renderer.RunAsync
        (graph,
         file,
         RendererLayouts.Dot,
         format,
         CancellationToken.None))
    do! file.FlushAsync()
}

// GraphVizのグラフ構築を簡略化出来るように関数化
let edge (node1: NodeId) (node2: NodeId) = EdgeStatement.For(node1, node2)
let nodeId (name: string) = NodeId(Id(name))

// 有向グラフのエッジを生成する演算子を定義
let inline (-->) nodeName1 nodeName2 = edge (nodeId nodeName1) (nodeId nodeName2)
let inline (<--) nodeName1 nodeName2 = edge (nodeId nodeName2) (nodeId nodeName1)

// 有向グラフにエッジを追加する演算子を定義
let inline (<<) (graph: Graph) e = graph.Add(e)

// 有向グラフを生成する関数
let genDirectedGraph() =
    // グラフが右から左に集約されていくように描画する
    // （左が最も
    Graph.Directed.Add(AttributeStatement.Graph.Set(Id("rankdir"), Id("RL")))

// 型名を文字列で取得します
let typeName (typ: Type) =
    let rec recTypeName (typ: Type) =
        // 型が総称型の場合は正しくレンダリングされないため、ここで再帰的に処理する
        let name =
            if typ.IsGenericType then
                let index = typ.Name.IndexOf '`'
                let name =
                    if index >= 0 then
                        typ.Name.Substring(0, index)
                    else
                        typ.Name
                let parameterTypesName =
                    typ.GetGenericArguments()
                    |> Seq.map(recTypeName)
                    |> Seq.reduce(fun name1 name2 -> name1 + ", " + name2)
                name + "<" + parameterTypesName + ">"
            else
                typ.Name
        // 型がネストした型の場合は外郭の型名を取得して結合する
        if (typ.DeclaringType <> null) && not typ.IsGenericParameter then
            (recTypeName typ.DeclaringType) + "." + name
        else
            name
    typ.Namespace + "." + (recTypeName typ)
    
// 2値タプルのシーケンスから辞書を生成する関数
let toDictionary (xs: ('T * 'U) seq) =
    new Dictionary<_, _>(xs |> Seq.map(fun (k, v) -> new KeyValuePair<_, _>(k, v))) :> IReadOnlyDictionary<_, _>

// 指定された関数が返す値が続く限り、個々の要素をシーケンスとして結合する関数
let traverse (predict: 'T -> 'T) (value: 'T) = seq {
    let mutable current = value
    while current <> null do
        yield current
        current <- predict current
}

//////////////////////////////////////////////////////////////////////////

// メインプログラム
let mainAsync argv = async {

    ////////////////////////////////////////////////////////////////////
    // 元となる情報を取得する

    // Core libraryの全ての型を取得し、その中から:
    //   1. クラス型・又は値型であること
    //   2. パブリックであること（ネストした型でパブリックなものも含む）
    // の両方の条件を満たす型を取得して、リストにする
    // （vertexに相当する）
    let types =
        typeof<obj>.Assembly.GetTypes()
        |> Seq.filter(fun typ -> (typ.IsClass || typ.IsValueType) && (typ.IsPublic || typ.IsNestedPublic))
        |> Seq.toList

    ////////////////////////////////////////////////////////////////////
    // 1. 集計処理

    // 各型から派生する型群を取得できる辞書を生成する。
    // 以下のような関係の型について、BaseTypeからDerivedType群を取得できる。
    // BaseType <--+-- DerivedType1
    //             +-- DerivedType2
    //             +-- DerivedType3
    let derivedTypes =
        types
        |> Seq.filter(fun typ -> typ.BaseType <> null)
        |> Seq.groupBy(fun typ -> typ.BaseType)
        |> Seq.map(fun (typ, derivedTypes) -> typ, derivedTypes |> Seq.toArray)
        |> toDictionary

    //////////////////////////////////
    // 1-1. 次数

    // 最大次数を計算する。
    // derivedTypesから最大の次数を検索する。
    let maxDegreeDistribution =
        derivedTypes |> Seq.map(fun kv -> kv.Value.Length) |> Seq.max

    // edgeの総数を得る。
    // derivedTypesの次数を全て加算する。
    let edgeCount =
        derivedTypes |> Seq.fold(fun v kv -> kv.Value.Length + v) 0

    // 平均次数を計算する。
    // derivedTypesの次数を全て加算（=edgeの総数）し、最大次数で割る。
    let averageForDegreeDistribution =
        (edgeCount |> float) / (maxDegreeDistribution |> float)

    // 次数分布を出力する。
    // 次数0についてはderivedTypesに含まれないため、出力されない。
    printfn "Degree distribution: %d / %d, Average=%f" derivedTypes.Count types.Length averageForDegreeDistribution
    // DerivedType群の量でソートして出力する。
    derivedTypes
        // 派生型が多い順にソートする
        |> Seq.sortByDescending(fun kv -> kv.Value.Length)
        |> Seq.iter(fun kv -> printfn "  %s: %d" (typeName kv.Key) (kv.Value.Length))

    printfn ""
    printfn "================================="

    //////////////////////////////////
    // 1-2. 密度

    // edgeの最大数を計算する。
    // 有向グラフなので： Emax = V(V - 1)
    let maxEdgeCount =
        types.Length * (types.Length - 1)

    // 密度を得る。
    let graphDensity =
        (edgeCount |> float) / (maxEdgeCount |> float)
    printfn ""
    printfn "Density: %f (%d / %d)" graphDensity edgeCount maxEdgeCount

    printfn ""
    printfn "================================="

    //////////////////////////////////
    // 1-3. 距離

    // 有向グラフの場合、到達不可能な型が存在すると、距離が無限大として定義される。
    // （そして.NETの型システムで、基底型へのedgeを扱う限り、必ず無限大になる）
    // ここでは、ある型がobj型（唯一の基底型）に到達できるので、この距離を算出してみる。
    // この距離がわかると、派生している型群の長短がわかる。
    // その結果、不用意に継承を行っている型がないかどうか、という事がわかるようになる。

    // obj <-- DerivedType1 <-- DerivedType2 <-- DerivedType3
    //      3                2                1

    // ある型が、obj型に到達するための距離を計算し、辞書化する。
    let distanceToObject =
        // 基底型（baseType）を辿り、obj型までの距離を辞書の値とする。
        types
        |> Seq.map(fun typ -> (typ, typ.BaseType |> traverse (fun typ -> typ.BaseType) |> Seq.length))
        |> toDictionary

    // 距離の平均を計算する。
    // 距離の合計を個数で割る。
    let averageForDistance =
        (distanceToObject
         |> Seq.map(fun kv -> kv.Value)
         |> Seq.reduce(fun v1 v2 -> v1 + v2)
         |> float)
        / (distanceToObject.Count |> float)

    printfn ""
    printfn "Distance: Average=%f" averageForDistance
    distanceToObject
        |> Seq.sortByDescending(fun kv -> kv.Value)
        |> Seq.iter(fun kv -> printfn "  %s: %d" (typeName kv.Key) kv.Value)

    printfn ""
    printfn "================================="
    
    //////////////////////////////////
    // 1-4. クラスター係数

    // 距離同様、ある型の基底型は、いづれobj型に到達するため、
    // クラスターを構成する集合は、以下のような場合に限られる:

    // obj <-- Type1 <--+-- DerivedType21
    //                  +-- DerivedType22 <--+-- DerivedType31
    //                  +-- DerivedType23    +-- DerivedType32
    //     [x]          [3]                  [2]
    
    // 上記の状態で、Cobj = (3 + 2) / (6 * (6 - 1)) = 5/30
    // 単一方向のedgeのみでグラフが構成されていると、クラスター係数は小さくなる。
    // （クラスター係数を計上するedgeは、一般の矢印とは逆方向で計算する）

    // 指定された型の派生型を全て探索し、全ての派生型数を取得する関数
    let calculateCluster typ =
        // fcは再帰探索する場合だけ、派生型の数を取得する関数（ts.Length）にすり替える。
        let rec sumEdges (fc: Type[] -> int) (typ: Type) : int =
            match derivedTypes.TryGetValue(typ) with
            // 派生型のリストが得られたら、それぞれについて再帰的に派生型を取得する
            | true, types -> (fc types) + (types |> Seq.map(sumEdges (fun ts -> ts.Length)) |> Seq.sum)
            | _ -> 0
        
        // fcの初期関数は常に0を返すので、最初のedge（objとその派生型間）は計上されない。
        let value = sumEdges (fun _ -> 0) typ
        (value |> float) / (types.Length |> float)

    //
    types |> Seq.iter(fun typ ->
        let cluster = calculateCluster typ
        printfn "  %s: %f" (typeName typ) (cluster))


    ////////////////////////////////////////////////////////////////////
    // 2. グラフを図に出力する

    // 全ての型を列挙して、その型の基底型が存在する場合に、有向グラフを構築する再帰関数
    let rec constructGraph dgraph (types: Type list) =
        match types with
        | typ :: types ->
            // （obj型には基底型が存在しないので念の為除外する）
            let baseType = typ.BaseType
            if baseType <> null then
                // 現在の型 --> 基底型  となる有向グラフのエッジを作る
                let edge = (typeName typ) --> (typeName baseType)
                // グラフに追加して、次の型を処理する
                constructGraph (dgraph << edge) types
            else
                constructGraph dgraph types
        | _ ->
            dgraph

    // 有向グラフを構築する
    let dgraph = types |> constructGraph (genDirectedGraph())

    // GraphVizを使用して、グラフを出力する
    do! dgraph |> renderAsync "test.svg" RendererFormats.Svg
}

[<EntryPoint>]
let main argv =
    // mainAsyncは非同期関数なので、ここで同期的に実行の完了を待機する
    mainAsync argv |> Async.RunSynchronously

    0
