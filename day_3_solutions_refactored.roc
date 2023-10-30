# See https://adventofcode.com/2021/day/3

app "solve_day_3"
    packages { pf: "./roc/examples/interactive/cli-platform/main.roc" }
    imports [
        pf.File,
        pf.Path,
        pf.Program.{ Program },
        pf.Stderr,
        pf.Stdout,
        pf.Task,
    ]
    provides [main] to pf

# Core of my solution (before seeing other people's solutions)

parseInputDataByJancvanb = \inputText ->
    inputText
    |> Str.trim
    |> Str.split "\n"
    |> List.mapTry (\line ->
        line
        |> Str.toUtf8
        |> List.mapTry (\character ->
            [character]
            |> Str.fromUtf8
            |> Result.try Str.toU32))

calculatePart1AnswerByJancvanb = \matrix ->
    columnSums = sumColumns matrix
    sumColumns = \matrix ->
        firstRow = List.first matrix |> Result.withDefault [0]
        otherRows = List.dropFirst matrix
        List.walk otherRows firstRow \columnSums, row ->
            List.map2 columnSums row Num.add
    gamma =
        columnSums
        |> List.map (\sum ->
            if sum * 2 > rowCount then
                1
            else
                0)
        |> (\digits ->
            digits
            |> List.reverse
            |> List.walk { n: 0, power: 0 } (\state, digit ->
                {
                    n: state.n + digit * Num.powInt 2 state.power,
                    power: state.power + 1,
                })
            |> .n)
    rowCount = matrix |> List.len |> Num.toU32
    columnCount = columnSums |> List.len |> Num.toU32
    maximumRow = Num.powInt 2 columnCount - 1
    epsilon = Num.bitwiseXor gamma maximumRow
    gamma * epsilon


calculatePart2AnswerByJancvanb = calculatePart1AnswerByJancvanb # TODO

# Core of @ghigt's solution, lightly reformatted
# See https://github.com/ghigt/advent-of-code/blob/main/roc/day-2/main.roc

parseInputDataByGhigt = \content ->
    content
    |> Str.trim
    |> Str.split "\n"

calculatePart1AnswerByGhigt : List Str -> Str
calculatePart1AnswerByGhigt = \lines ->
    lineLength = \list ->
        List.takeFirst list 1 |> List.map Str.countGraphemes |> List.sum
    lines
    |> List.walk
        (List.repeat 0 (lineLength lines))
        (
            \list, line ->
                Str.toScalars line
                |> List.map2
                    list
                    \x, y ->
                        when x is
                            49 -> y + 1
                            _ -> y
        )
    |> \list ->
        compute = \list, len, cmp ->
            list
            |> compare (Num.toFrac len) cmp
            |> transformByGhigt
        compare = \list, len, cmp ->
            List.map list \x ->
                if cmp (len - x) (len / 2) then "1" else "0"
        a = compute list (List.len lines) Num.isGte
        b = compute list (List.len lines) Num.isLt
        a * b
    |> Num.toStr

transformByGhigt = \list ->
    list
    |> Str.joinWith ""
    |> (\x -> Str.concat "0b" x)
    |> Str.toU64
    |> Result.withDefault 0

calculatePart2AnswerByGhigt = \lines ->
    process = \lines, cmp ->
        List.range 0 12
        |> List.walk lines (\list, idx ->
            if List.len list == 1 then
                list
            else
                splitZeroOneAt list idx
                |> cmp
        )
        |> transformByGhigt
    splitZeroOneAt = \lines, idx ->
        lines
        |> List.walk { zero: [], one: [] } (\{ zero, one }, line ->
            n = Str.toUtf8 line |> List.get idx |> Result.withDefault 0

            if n == 48 then
                { one, zero: List.append zero line }
            else
                { zero, one: List.append one line }
        )
    cmpFirst = \{ zero, one } ->
        if List.len one >= List.len zero then one else zero
    cmpSec = \{ zero, one } ->
        if List.len zero <= List.len one then zero else one
    (process lines cmpFirst) * (process lines cmpSec)

# Core of @bhansconnect's solution
# See https://github.com/bhansconnect/roc-aoc-2021/blob/trunk/day3/part1.roc
# and https://github.com/bhansconnect/roc-aoc-2021/blob/trunk/day3/part2.roc

parseInputDataByBhansconnect = \contents ->
    contents
    |> Str.trim
    |> Str.split "\n"
    |> List.map Str.toUtf8
    # Convert from utf8 to real numbers
    |> List.map (\l -> List.map l (\x -> (Num.toU64 x) - 48))

calculatePart1AnswerByBhansconnect : List (List U64) -> U64
calculatePart1AnswerByBhansconnect = \data ->
    len = Num.toU64 (List.len data)
    List.walk data [] (\accum, next ->
        if List.isEmpty accum then
            next
        else
            List.map2 accum next Num.add
    ) |> List.walk (T 0 0) (\T gamma epsilon, bitCount ->
        shiftedGamma = Num.shiftLeftBy gamma 1
        shiftedEpsilon = Num.shiftLeftBy epsilon 1
        if bitCount > len - bitCount then
            T (shiftedGamma + 1) shiftedEpsilon
        else
            T shiftedGamma (shiftedEpsilon + 1)
    ) |> (\T gamma epsilon -> gamma * epsilon)

calculatePart2AnswerByBhansconnect : List (List U64) -> U64
calculatePart2AnswerByBhansconnect = \data ->
    filterData : List (List U64), Nat, Bool -> List (List U64) 
    filterData = \data, i, keepCommon ->
        len = Num.toU64 (List.len data)
        if len == 1 then
            data
        else
            count = List.walk data 0 (\accum, currentBits ->
                when List.get currentBits i is
                    Ok bit ->
                        bit + accum
                    Err _ ->
                        # This shouldn't be possible, just panic.
                        # I should probably bubble up results cleanly and do this right.
                        x : U64
                        x = 0 - 1
                        x
                )
            commonBit = if count >= len - count then 1 else 0
            filtered = List.keepIf data (\currentBits ->
                when List.get currentBits i is
                    Ok bit ->
                        (keepCommon && bit == commonBit) || (!keepCommon && bit != commonBit)
                    Err _ ->
                        # Same here, this should fail and bubble up.
                        # Though again. it isn't possible.
                        Bool.false
                )
            filterData filtered (i + 1) keepCommon
    oxygen = filterData data 0 Bool.true
    co2 = filterData data 0 Bool.false
    toDecimal : List U64 -> U64
    toDecimal = \list ->
        accum, bit <- List.walk list 0
        bit + Num.shiftLeftBy accum 1
    when T (List.first oxygen) (List.first co2) is
        T (Ok x) (Ok y) -> (toDecimal x) * (toDecimal y)
        _ ->
            # This shouldn't be possible, just panic.
            # I should probably bubble up results cleanly and do this right.
            x : U64
            x = 0 - 1
            x

# Core of @shritesh's solution, refactored lightly
# See https://github.com/shritesh/advent/blob/main/2021/3.roc

parseInputDataByShritesh = \input ->
    strs =
        input
        |> Str.trim
        |> Str.split "\n"
    # poor man's clz-ish
    len =
        List.takeFirst strs 1
        |> List.map Str.countGraphemes
        |> List.sum
    numbers = List.map strs \line ->
        Str.walkScalars line 0 \n, s ->
            if s == '1' then
                Num.shiftLeftBy n 1 + 1
            else
                # Should error on invalid chars
                # but walkTry is not exposed to userspace
                Num.shiftLeftBy n 1
    { numbers, len }

calculatePart1AnswerByShritesh = \{ numbers, len } ->
    setBit = \num, index ->
        Num.bitwiseOr num (maskByShritesh index)
    rates = List.walk (List.range 0 len) { gamma: 0, epsilon: 0 } \{ gamma, epsilon }, index ->
        { zeroes, ones } = bitCountByShritesh numbers index
        if ones > zeroes then
            # isGammaOne
            { gamma: setBit gamma index, epsilon }
        else if zeroes > ones then
            # isEpsilonOne
            { gamma, epsilon: setBit epsilon index }
        else
            { gamma, epsilon }
    rates.gamma * rates.epsilon

bitCountByShritesh = \numbers, index ->
    List.walk numbers { zeroes: 0, ones: 0 } \{ zeroes, ones }, num ->
        if Num.bitwiseAnd num (maskByShritesh index) == 0 then
            { zeroes: zeroes + 1, ones }
        else
            { zeroes, ones: ones + 1 }
maskByShritesh = \index -> Num.shiftLeftBy 1 index

calculatePart2AnswerByShritesh = \{ numbers, len } ->
    criteria = \numbers, len, which, tieBreaker ->
        List.walkUntil (List.range 0 len) numbers \nums, index ->
            if List.len nums == 1 then
                Break nums
            else
                actualIndex = len - index - 1
                { zeroes, ones } = bitCountByShritesh nums actualIndex
                keep = 
                    when which is
                        Most ->
                            if zeroes > ones then
                                0
                            else if ones > zeroes then
                                1
                            else
                                tieBreaker
                        Least ->
                            if zeroes < ones then
                                0
                            else if ones < zeroes then
                                1
                            else
                                tieBreaker
                Continue (filter nums actualIndex keep)
    filter = \numbers, index, keep ->
        zeroAtIndex = \num -> Num.bitwiseAnd num (maskByShritesh index) == 0
        if keep == 0 then
            List.keepIf numbers zeroAtIndex
        else
            List.dropIf numbers zeroAtIndex
    oxygen = criteria numbers len Most 1
    co2 = criteria numbers len Least 0
    List.join [oxygen, co2]
    |> List.product

################################################################################
################################################################################
################################################################################

# Problem-agnostic boilerplate

main =
    "day_3_input.txt"
    |> solve
    |> Task.attempt exit
    |> Program.noArgs

solve = \inputDataFileName ->
    inputText <-
        inputDataFileName
        |> Path.fromStr
        |> File.readUtf8
        |> Task.await
    when parseInputData inputText is
        Ok inputData -> Task.succeed (Answers
            (calculatePart1Answer inputData)
            (calculatePart2Answer inputData))
        Err _ -> Task.fail DataParseError

exit = \result ->
    when result is
        Ok answers -> succeed answers
        Err error -> fail error

succeed = \Answers part1Answer part2Answer ->
    a1 = Num.toStr part1Answer
    a2 = Num.toStr part2Answer
    "Answer to part 1: \(a1)\nAnswer to part 2: \(a2)"
    |> Stdout.line 
    |> Program.exit 0

fail = \error ->
    errorMessage =
        when error is
            FileReadError _ _ ->
                "Failed to read input data file!"
            DataParseError ->
                "Failed to parse input data!"
            _ ->
                "An unknown error occurred!"
    Stderr.line errorMessage
    |> Program.exit 1

parseInputData = parseInputDataByJancvanb

calculatePart1Answer = calculatePart1AnswerByJancvanb

calculatePart2Answer = calculatePart2AnswerByJancvanb
