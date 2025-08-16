---- MODULE quicksort ----
EXTENDS TLC, Integers, Sequences

CONSTANTS 
    NULL,
    MaxArrayLength,
    Items

Sorted(array) ==
    \A i \in 1..Len(array) - 1:
        array[i] <= array[i + 1]

IsLeqMin(array, x) ==
    \A i \in 1..Len(array): x <= array[i]

PossibleInputs ==
    UNION {[1..n -> Items]: n \in 0..MaxArrayLength}

(*--fair algorithm quicksort
variables
    array \in PossibleInputs,
    mid;

procedure partition(left, right, pivot)
variables
    l,
    r;
begin
    Partition:
        assert left < right;
        assert ~IsLeqMin(array, pivot);

        l := left;
        r := right;

        PartitionLoop:
            while l < r do
                SearchLeft:
                    while l <= right /\ array[l] < pivot do
                        l := l + 1;
                    end while;
                
                SearchRight:
                    while left <= r /\ array[r] >= pivot do
                        r := r - 1;
                    end while;

                if l < r then
                    with tmp = array[l] do
                        array[l] := array[r] ||
                        array[r] := tmp;
                    end with;
                end if;
            end while;

            mid := l;
        return;
end procedure;

procedure sort(left, right) 
variables
    i,
    pivotValue;
begin
    QuickSort:
        if left < right then
            i := left + 1;
            FindPivot:
                while i <= right do
                    if array[i] < array[left] then
                        pivotValue := array[left];
                        goto FoundPivot;
                    elsif i < right /\ array[i] > array[left] then
                        pivotValue := array[i];
                        goto FoundPivot;
                    end if;

                    IncrementI:
                        i := i + 1;
                end while;

                assert pivotValue = NULL;
                goto CheckSubArraySorted;

            FoundPivot:
                call partition(left, right, pivotValue);
            SortLeft:
                call sort(left, mid - 1);
            SortRight:
                call sort(mid, right);
        end if;
    CheckSubArraySorted:
        assert Sorted(SubSeq(array, left, right));
    return;
end procedure;

process main = "main"
begin
    Main:
        call sort(1, Len(array));
    CheckSorted:
        assert Sorted(array);
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "e252c04e")
\* Parameter left of procedure partition at line 24 col 21 changed to left_
\* Parameter right of procedure partition at line 24 col 27 changed to right_
CONSTANT defaultInitValue
VARIABLES pc, array, mid, stack, left_, right_, pivot, l, r, left, right, i, 
          pivotValue

vars == << pc, array, mid, stack, left_, right_, pivot, l, r, left, right, i, 
           pivotValue >>

ProcSet == {"main"}

Init == (* Global variables *)
        /\ array \in PossibleInputs
        /\ mid = defaultInitValue
        (* Procedure partition *)
        /\ left_ = [ self \in ProcSet |-> defaultInitValue]
        /\ right_ = [ self \in ProcSet |-> defaultInitValue]
        /\ pivot = [ self \in ProcSet |-> defaultInitValue]
        /\ l = [ self \in ProcSet |-> defaultInitValue]
        /\ r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure sort *)
        /\ left = [ self \in ProcSet |-> defaultInitValue]
        /\ right = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ pivotValue = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Main"]

Partition(self) == /\ pc[self] = "Partition"
                   /\ Assert(left_[self] < right_[self], 
                             "Failure of assertion at line 30, column 9.")
                   /\ Assert(~IsLeqMin(array, pivot[self]), 
                             "Failure of assertion at line 31, column 9.")
                   /\ l' = [l EXCEPT ![self] = left_[self]]
                   /\ r' = [r EXCEPT ![self] = right_[self]]
                   /\ pc' = [pc EXCEPT ![self] = "PartitionLoop"]
                   /\ UNCHANGED << array, mid, stack, left_, right_, pivot, 
                                   left, right, i, pivotValue >>

PartitionLoop(self) == /\ pc[self] = "PartitionLoop"
                       /\ IF l[self] < r[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "SearchLeft"]
                                  /\ UNCHANGED << mid, stack, left_, right_, 
                                                  pivot, l, r >>
                             ELSE /\ mid' = l[self]
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ l' = [l EXCEPT ![self] = Head(stack[self]).l]
                                  /\ r' = [r EXCEPT ![self] = Head(stack[self]).r]
                                  /\ left_' = [left_ EXCEPT ![self] = Head(stack[self]).left_]
                                  /\ right_' = [right_ EXCEPT ![self] = Head(stack[self]).right_]
                                  /\ pivot' = [pivot EXCEPT ![self] = Head(stack[self]).pivot]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << array, left, right, i, pivotValue >>

SearchLeft(self) == /\ pc[self] = "SearchLeft"
                    /\ IF l[self] <= right_[self] /\ array[l[self]] < pivot[self]
                          THEN /\ l' = [l EXCEPT ![self] = l[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "SearchLeft"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "SearchRight"]
                               /\ l' = l
                    /\ UNCHANGED << array, mid, stack, left_, right_, pivot, r, 
                                    left, right, i, pivotValue >>

SearchRight(self) == /\ pc[self] = "SearchRight"
                     /\ IF left_[self] <= r[self] /\ array[r[self]] >= pivot[self]
                           THEN /\ r' = [r EXCEPT ![self] = r[self] - 1]
                                /\ pc' = [pc EXCEPT ![self] = "SearchRight"]
                                /\ array' = array
                           ELSE /\ IF l[self] < r[self]
                                      THEN /\ LET tmp == array[l[self]] IN
                                                array' = [array EXCEPT ![l[self]] = array[r[self]],
                                                                       ![r[self]] = tmp]
                                      ELSE /\ TRUE
                                           /\ array' = array
                                /\ pc' = [pc EXCEPT ![self] = "PartitionLoop"]
                                /\ r' = r
                     /\ UNCHANGED << mid, stack, left_, right_, pivot, l, left, 
                                     right, i, pivotValue >>

partition(self) == Partition(self) \/ PartitionLoop(self)
                      \/ SearchLeft(self) \/ SearchRight(self)

QuickSort(self) == /\ pc[self] = "QuickSort"
                   /\ IF left[self] < right[self]
                         THEN /\ i' = [i EXCEPT ![self] = left[self] + 1]
                              /\ pc' = [pc EXCEPT ![self] = "FindPivot"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "CheckSubArraySorted"]
                              /\ i' = i
                   /\ UNCHANGED << array, mid, stack, left_, right_, pivot, l, 
                                   r, left, right, pivotValue >>

FindPivot(self) == /\ pc[self] = "FindPivot"
                   /\ IF i[self] <= right[self]
                         THEN /\ IF array[i[self]] < array[left[self]]
                                    THEN /\ pivotValue' = [pivotValue EXCEPT ![self] = array[left[self]]]
                                         /\ pc' = [pc EXCEPT ![self] = "FoundPivot"]
                                    ELSE /\ IF i[self] < right[self] /\ array[i[self]] > array[left[self]]
                                               THEN /\ pivotValue' = [pivotValue EXCEPT ![self] = array[i[self]]]
                                                    /\ pc' = [pc EXCEPT ![self] = "FoundPivot"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "IncrementI"]
                                                    /\ UNCHANGED pivotValue
                         ELSE /\ Assert(pivotValue[self] = NULL, 
                                        "Failure of assertion at line 82, column 17.")
                              /\ pc' = [pc EXCEPT ![self] = "CheckSubArraySorted"]
                              /\ UNCHANGED pivotValue
                   /\ UNCHANGED << array, mid, stack, left_, right_, pivot, l, 
                                   r, left, right, i >>

IncrementI(self) == /\ pc[self] = "IncrementI"
                    /\ i' = [i EXCEPT ![self] = i[self] + 1]
                    /\ pc' = [pc EXCEPT ![self] = "FindPivot"]
                    /\ UNCHANGED << array, mid, stack, left_, right_, pivot, l, 
                                    r, left, right, pivotValue >>

FoundPivot(self) == /\ pc[self] = "FoundPivot"
                    /\ /\ left_' = [left_ EXCEPT ![self] = left[self]]
                       /\ pivot' = [pivot EXCEPT ![self] = pivotValue[self]]
                       /\ right_' = [right_ EXCEPT ![self] = right[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "partition",
                                                                pc        |->  "SortLeft",
                                                                l         |->  l[self],
                                                                r         |->  r[self],
                                                                left_     |->  left_[self],
                                                                right_    |->  right_[self],
                                                                pivot     |->  pivot[self] ] >>
                                                            \o stack[self]]
                    /\ l' = [l EXCEPT ![self] = defaultInitValue]
                    /\ r' = [r EXCEPT ![self] = defaultInitValue]
                    /\ pc' = [pc EXCEPT ![self] = "Partition"]
                    /\ UNCHANGED << array, mid, left, right, i, pivotValue >>

SortLeft(self) == /\ pc[self] = "SortLeft"
                  /\ /\ left' = [left EXCEPT ![self] = left[self]]
                     /\ right' = [right EXCEPT ![self] = mid - 1]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sort",
                                                              pc        |->  "SortRight",
                                                              i         |->  i[self],
                                                              pivotValue |->  pivotValue[self],
                                                              left      |->  left[self],
                                                              right     |->  right[self] ] >>
                                                          \o stack[self]]
                  /\ i' = [i EXCEPT ![self] = defaultInitValue]
                  /\ pivotValue' = [pivotValue EXCEPT ![self] = defaultInitValue]
                  /\ pc' = [pc EXCEPT ![self] = "QuickSort"]
                  /\ UNCHANGED << array, mid, left_, right_, pivot, l, r >>

SortRight(self) == /\ pc[self] = "SortRight"
                   /\ /\ left' = [left EXCEPT ![self] = mid]
                      /\ right' = [right EXCEPT ![self] = right[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sort",
                                                               pc        |->  "CheckSubArraySorted",
                                                               i         |->  i[self],
                                                               pivotValue |->  pivotValue[self],
                                                               left      |->  left[self],
                                                               right     |->  right[self] ] >>
                                                           \o stack[self]]
                   /\ i' = [i EXCEPT ![self] = defaultInitValue]
                   /\ pivotValue' = [pivotValue EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "QuickSort"]
                   /\ UNCHANGED << array, mid, left_, right_, pivot, l, r >>

CheckSubArraySorted(self) == /\ pc[self] = "CheckSubArraySorted"
                             /\ Assert(Sorted(SubSeq(array, left[self], right[self])), 
                                       "Failure of assertion at line 93, column 9.")
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                             /\ pivotValue' = [pivotValue EXCEPT ![self] = Head(stack[self]).pivotValue]
                             /\ left' = [left EXCEPT ![self] = Head(stack[self]).left]
                             /\ right' = [right EXCEPT ![self] = Head(stack[self]).right]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << array, mid, left_, right_, pivot, 
                                             l, r >>

sort(self) == QuickSort(self) \/ FindPivot(self) \/ IncrementI(self)
                 \/ FoundPivot(self) \/ SortLeft(self) \/ SortRight(self)
                 \/ CheckSubArraySorted(self)

Main == /\ pc["main"] = "Main"
        /\ /\ left' = [left EXCEPT !["main"] = 1]
           /\ right' = [right EXCEPT !["main"] = Len(array)]
           /\ stack' = [stack EXCEPT !["main"] = << [ procedure |->  "sort",
                                                      pc        |->  "CheckSorted",
                                                      i         |->  i["main"],
                                                      pivotValue |->  pivotValue["main"],
                                                      left      |->  left["main"],
                                                      right     |->  right["main"] ] >>
                                                  \o stack["main"]]
        /\ i' = [i EXCEPT !["main"] = defaultInitValue]
        /\ pivotValue' = [pivotValue EXCEPT !["main"] = defaultInitValue]
        /\ pc' = [pc EXCEPT !["main"] = "QuickSort"]
        /\ UNCHANGED << array, mid, left_, right_, pivot, l, r >>

CheckSorted == /\ pc["main"] = "CheckSorted"
               /\ Assert(Sorted(array), 
                         "Failure of assertion at line 102, column 9.")
               /\ pc' = [pc EXCEPT !["main"] = "Done"]
               /\ UNCHANGED << array, mid, stack, left_, right_, pivot, l, r, 
                               left, right, i, pivotValue >>

main == Main \/ CheckSorted

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: partition(self) \/ sort(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

StackLenLimit == \A self \in ProcSet: Len(stack[self]) < 20

====
