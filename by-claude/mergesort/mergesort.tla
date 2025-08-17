---- MODULE mergesort ----
EXTENDS TLC, Integers, Sequences

CONSTANTS 
    MaxArrayLength,
    Items

Sorted(array) ==
    \A i \in 1..Len(array)-1:
        array[i] <= array[i + 1]

PossibleInputs ==
    UNION {[1..n -> Items] : n \in 1..MaxArrayLength}

\* Helper functions for mergesort
Min(a, b) == IF a <= b THEN a ELSE b

(*--fair algorithm mergesort
variables
    array \in PossibleInputs,
    temp = <<>>,
    i = 1,
    j = 1,
    k = 1,
    size = 1,
    leftStart = 1,
    leftEnd = 1,
    rightStart = 1, 
    rightEnd = 1,
    n = Len(array),
    leftArr = <<>>,
    rightArr = <<>>,
    l = 1,
    m = 1,
    r = 1;

procedure merge(left, mid, right)
variables
    li = 1,
    ri = 1,
    ki = left;
begin
    MergeStart:
        leftArr := SubSeq(array, left, mid);
        rightArr := SubSeq(array, mid + 1, right);
        li := 1;
        ri := 1;
        ki := left;
    MergeMainLoop:
        while (li <= Len(leftArr) /\ ri <= Len(rightArr)) do
            if leftArr[li] <= rightArr[ri] then
                array[ki] := leftArr[li];
                li := li + 1;
            else
                array[ki] := rightArr[ri];
                ri := ri + 1;
            end if;
            ki := ki + 1;
        end while;
    MergeLeftLoop:
        while (li <= Len(leftArr)) do
            array[ki] := leftArr[li];
            li := li + 1;
            ki := ki + 1;
        end while;
    MergeRightLoop:
        while (ri <= Len(rightArr)) do
            array[ki] := rightArr[ri];
            ri := ri + 1;
            ki := ki + 1;
        end while;
    MergeDone:
        return;
end procedure;

procedure sort()
begin
    StartMergeSort:
        size := 1;
    MergeSortLoop:
        while size < n do
            leftStart := 1;
        InnerLoop:
            while leftStart <= n - size do
                leftEnd := leftStart + size - 1;
                rightStart := leftEnd + 1;
                rightEnd := Min(leftStart + 2 * size - 1, n);
            DoMerge:
                call merge(leftStart, leftEnd, rightEnd);
            UpdateLeftStart:
                leftStart := leftStart + 2 * size;
            end while;
        UpdateSize:
            size := 2 * size;
        end while;
    DoneSorting:
        return;
end procedure;

process main = "main"
begin
    Main:
        call sort();
    CheckSorted:
        assert Sorted(array);
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "df941475" /\ chksum(tla) = "b5cb5e3f")
CONSTANT defaultInitValue
VARIABLES array, temp, i, j, k, size, leftStart, leftEnd, rightStart, 
          rightEnd, n, leftArr, rightArr, l, m, r, pc, stack, left, mid, 
          right, li, ri, ki

vars == << array, temp, i, j, k, size, leftStart, leftEnd, rightStart, 
           rightEnd, n, leftArr, rightArr, l, m, r, pc, stack, left, mid, 
           right, li, ri, ki >>

ProcSet == {"main"}

Init == (* Global variables *)
        /\ array \in PossibleInputs
        /\ temp = <<>>
        /\ i = 1
        /\ j = 1
        /\ k = 1
        /\ size = 1
        /\ leftStart = 1
        /\ leftEnd = 1
        /\ rightStart = 1
        /\ rightEnd = 1
        /\ n = Len(array)
        /\ leftArr = <<>>
        /\ rightArr = <<>>
        /\ l = 1
        /\ m = 1
        /\ r = 1
        (* Procedure merge *)
        /\ left = [ self \in ProcSet |-> defaultInitValue]
        /\ mid = [ self \in ProcSet |-> defaultInitValue]
        /\ right = [ self \in ProcSet |-> defaultInitValue]
        /\ li = [ self \in ProcSet |-> 1]
        /\ ri = [ self \in ProcSet |-> 1]
        /\ ki = [ self \in ProcSet |-> left[self]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Main"]

MergeStart(self) == /\ pc[self] = "MergeStart"
                    /\ leftArr' = SubSeq(array, left[self], mid[self])
                    /\ rightArr' = SubSeq(array, mid[self] + 1, right[self])
                    /\ li' = [li EXCEPT ![self] = 1]
                    /\ ri' = [ri EXCEPT ![self] = 1]
                    /\ ki' = [ki EXCEPT ![self] = left[self]]
                    /\ pc' = [pc EXCEPT ![self] = "MergeMainLoop"]
                    /\ UNCHANGED << array, temp, i, j, k, size, leftStart, 
                                    leftEnd, rightStart, rightEnd, n, l, m, r, 
                                    stack, left, mid, right >>

MergeMainLoop(self) == /\ pc[self] = "MergeMainLoop"
                       /\ IF (li[self] <= Len(leftArr) /\ ri[self] <= Len(rightArr))
                             THEN /\ IF leftArr[li[self]] <= rightArr[ri[self]]
                                        THEN /\ array' = [array EXCEPT ![ki[self]] = leftArr[li[self]]]
                                             /\ li' = [li EXCEPT ![self] = li[self] + 1]
                                             /\ ri' = ri
                                        ELSE /\ array' = [array EXCEPT ![ki[self]] = rightArr[ri[self]]]
                                             /\ ri' = [ri EXCEPT ![self] = ri[self] + 1]
                                             /\ li' = li
                                  /\ ki' = [ki EXCEPT ![self] = ki[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "MergeMainLoop"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MergeLeftLoop"]
                                  /\ UNCHANGED << array, li, ri, ki >>
                       /\ UNCHANGED << temp, i, j, k, size, leftStart, leftEnd, 
                                       rightStart, rightEnd, n, leftArr, 
                                       rightArr, l, m, r, stack, left, mid, 
                                       right >>

MergeLeftLoop(self) == /\ pc[self] = "MergeLeftLoop"
                       /\ IF (li[self] <= Len(leftArr))
                             THEN /\ array' = [array EXCEPT ![ki[self]] = leftArr[li[self]]]
                                  /\ li' = [li EXCEPT ![self] = li[self] + 1]
                                  /\ ki' = [ki EXCEPT ![self] = ki[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "MergeLeftLoop"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MergeRightLoop"]
                                  /\ UNCHANGED << array, li, ki >>
                       /\ UNCHANGED << temp, i, j, k, size, leftStart, leftEnd, 
                                       rightStart, rightEnd, n, leftArr, 
                                       rightArr, l, m, r, stack, left, mid, 
                                       right, ri >>

MergeRightLoop(self) == /\ pc[self] = "MergeRightLoop"
                        /\ IF (ri[self] <= Len(rightArr))
                              THEN /\ array' = [array EXCEPT ![ki[self]] = rightArr[ri[self]]]
                                   /\ ri' = [ri EXCEPT ![self] = ri[self] + 1]
                                   /\ ki' = [ki EXCEPT ![self] = ki[self] + 1]
                                   /\ pc' = [pc EXCEPT ![self] = "MergeRightLoop"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "MergeDone"]
                                   /\ UNCHANGED << array, ri, ki >>
                        /\ UNCHANGED << temp, i, j, k, size, leftStart, 
                                        leftEnd, rightStart, rightEnd, n, 
                                        leftArr, rightArr, l, m, r, stack, 
                                        left, mid, right, li >>

MergeDone(self) == /\ pc[self] = "MergeDone"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ li' = [li EXCEPT ![self] = Head(stack[self]).li]
                   /\ ri' = [ri EXCEPT ![self] = Head(stack[self]).ri]
                   /\ ki' = [ki EXCEPT ![self] = Head(stack[self]).ki]
                   /\ left' = [left EXCEPT ![self] = Head(stack[self]).left]
                   /\ mid' = [mid EXCEPT ![self] = Head(stack[self]).mid]
                   /\ right' = [right EXCEPT ![self] = Head(stack[self]).right]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << array, temp, i, j, k, size, leftStart, 
                                   leftEnd, rightStart, rightEnd, n, leftArr, 
                                   rightArr, l, m, r >>

merge(self) == MergeStart(self) \/ MergeMainLoop(self)
                  \/ MergeLeftLoop(self) \/ MergeRightLoop(self)
                  \/ MergeDone(self)

StartMergeSort(self) == /\ pc[self] = "StartMergeSort"
                        /\ size' = 1
                        /\ pc' = [pc EXCEPT ![self] = "MergeSortLoop"]
                        /\ UNCHANGED << array, temp, i, j, k, leftStart, 
                                        leftEnd, rightStart, rightEnd, n, 
                                        leftArr, rightArr, l, m, r, stack, 
                                        left, mid, right, li, ri, ki >>

MergeSortLoop(self) == /\ pc[self] = "MergeSortLoop"
                       /\ IF size < n
                             THEN /\ leftStart' = 1
                                  /\ pc' = [pc EXCEPT ![self] = "InnerLoop"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "DoneSorting"]
                                  /\ UNCHANGED leftStart
                       /\ UNCHANGED << array, temp, i, j, k, size, leftEnd, 
                                       rightStart, rightEnd, n, leftArr, 
                                       rightArr, l, m, r, stack, left, mid, 
                                       right, li, ri, ki >>

InnerLoop(self) == /\ pc[self] = "InnerLoop"
                   /\ IF leftStart <= n - size
                         THEN /\ leftEnd' = leftStart + size - 1
                              /\ rightStart' = leftEnd' + 1
                              /\ rightEnd' = Min(leftStart + 2 * size - 1, n)
                              /\ pc' = [pc EXCEPT ![self] = "DoMerge"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateSize"]
                              /\ UNCHANGED << leftEnd, rightStart, rightEnd >>
                   /\ UNCHANGED << array, temp, i, j, k, size, leftStart, n, 
                                   leftArr, rightArr, l, m, r, stack, left, 
                                   mid, right, li, ri, ki >>

DoMerge(self) == /\ pc[self] = "DoMerge"
                 /\ /\ left' = [left EXCEPT ![self] = leftStart]
                    /\ mid' = [mid EXCEPT ![self] = leftEnd]
                    /\ right' = [right EXCEPT ![self] = rightEnd]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "merge",
                                                             pc        |->  "UpdateLeftStart",
                                                             li        |->  li[self],
                                                             ri        |->  ri[self],
                                                             ki        |->  ki[self],
                                                             left      |->  left[self],
                                                             mid       |->  mid[self],
                                                             right     |->  right[self] ] >>
                                                         \o stack[self]]
                 /\ li' = [li EXCEPT ![self] = 1]
                 /\ ri' = [ri EXCEPT ![self] = 1]
                 /\ ki' = [ki EXCEPT ![self] = left'[self]]
                 /\ pc' = [pc EXCEPT ![self] = "MergeStart"]
                 /\ UNCHANGED << array, temp, i, j, k, size, leftStart, 
                                 leftEnd, rightStart, rightEnd, n, leftArr, 
                                 rightArr, l, m, r >>

UpdateLeftStart(self) == /\ pc[self] = "UpdateLeftStart"
                         /\ leftStart' = leftStart + 2 * size
                         /\ pc' = [pc EXCEPT ![self] = "InnerLoop"]
                         /\ UNCHANGED << array, temp, i, j, k, size, leftEnd, 
                                         rightStart, rightEnd, n, leftArr, 
                                         rightArr, l, m, r, stack, left, mid, 
                                         right, li, ri, ki >>

UpdateSize(self) == /\ pc[self] = "UpdateSize"
                    /\ size' = 2 * size
                    /\ pc' = [pc EXCEPT ![self] = "MergeSortLoop"]
                    /\ UNCHANGED << array, temp, i, j, k, leftStart, leftEnd, 
                                    rightStart, rightEnd, n, leftArr, rightArr, 
                                    l, m, r, stack, left, mid, right, li, ri, 
                                    ki >>

DoneSorting(self) == /\ pc[self] = "DoneSorting"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << array, temp, i, j, k, size, leftStart, 
                                     leftEnd, rightStart, rightEnd, n, leftArr, 
                                     rightArr, l, m, r, left, mid, right, li, 
                                     ri, ki >>

sort(self) == StartMergeSort(self) \/ MergeSortLoop(self)
                 \/ InnerLoop(self) \/ DoMerge(self)
                 \/ UpdateLeftStart(self) \/ UpdateSize(self)
                 \/ DoneSorting(self)

Main == /\ pc["main"] = "Main"
        /\ stack' = [stack EXCEPT !["main"] = << [ procedure |->  "sort",
                                                   pc        |->  "CheckSorted" ] >>
                                               \o stack["main"]]
        /\ pc' = [pc EXCEPT !["main"] = "StartMergeSort"]
        /\ UNCHANGED << array, temp, i, j, k, size, leftStart, leftEnd, 
                        rightStart, rightEnd, n, leftArr, rightArr, l, m, r, 
                        left, mid, right, li, ri, ki >>

CheckSorted == /\ pc["main"] = "CheckSorted"
               /\ Assert(Sorted(array), 
                         "Failure of assertion at line 137, column 9.")
               /\ pc' = [pc EXCEPT !["main"] = "Done"]
               /\ UNCHANGED << array, temp, i, j, k, size, leftStart, leftEnd, 
                               rightStart, rightEnd, n, leftArr, rightArr, l, 
                               m, r, stack, left, mid, right, li, ri, ki >>

main == Main \/ CheckSorted

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: merge(self) \/ sort(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
