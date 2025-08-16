---- MODULE quicksort ----
EXTENDS TLC, Integers, Sequences

CONSTANTS 
    NULL,
    MaxArrayLength,
    Items

Sorted(array) ==
    \A i \in 1..Len(array) - 1:
        array[i] <= array[i + 1]

(*
PossibleInputs ==
    UNION {[1..n -> Items]: n \in 0..MaxArrayLength}
*)
PossibleInputs == [1..MaxArrayLength -> Items]

(*--fair algorithm quicksort
variables
    array \in PossibleInputs,
    mid;

procedure partition2(left, right)
variables
    pivot, i, j;
begin
    Partition:
        assert left < right;

        pivot := array[right];
        i := left;
        j := left;

        PartitionLoop:
            while j <= right do
                if array[j] < pivot then
                    with tmp = array[j] do
                        array[j] := array[i] ||
                        array[i] := tmp
                    end with;
                    i := i + 1;
                end if;
                j := j + 1;
            end while;

            with tmp = array[i] do
                array[i] := array[right] ||
                array[right] := tmp;
            end with;

            mid := i;
            return;
end procedure;

procedure sort(left, right) 
begin
    QuickSort:
        if left < right then
                call partition2(left, right);
            SortLeft:
                call sort(left, mid - 1);
            SortRight:
                call sort(mid + 1, right);
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
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "26132d9")
\* Parameter left of procedure partition2 at line 24 col 22 changed to left_
\* Parameter right of procedure partition2 at line 24 col 28 changed to right_
CONSTANT defaultInitValue
VARIABLES pc, array, mid, stack, left_, right_, pivot, i, j, left, right

vars == << pc, array, mid, stack, left_, right_, pivot, i, j, left, right >>

ProcSet == {"main"}

Init == (* Global variables *)
        /\ array \in PossibleInputs
        /\ mid = defaultInitValue
        (* Procedure partition2 *)
        /\ left_ = [ self \in ProcSet |-> defaultInitValue]
        /\ right_ = [ self \in ProcSet |-> defaultInitValue]
        /\ pivot = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ j = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure sort *)
        /\ left = [ self \in ProcSet |-> defaultInitValue]
        /\ right = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Main"]

Partition(self) == /\ pc[self] = "Partition"
                   /\ Assert(left_[self] < right_[self], 
                             "Failure of assertion at line 29, column 9.")
                   /\ pivot' = [pivot EXCEPT ![self] = array[right_[self]]]
                   /\ i' = [i EXCEPT ![self] = left_[self]]
                   /\ j' = [j EXCEPT ![self] = left_[self]]
                   /\ pc' = [pc EXCEPT ![self] = "PartitionLoop"]
                   /\ UNCHANGED << array, mid, stack, left_, right_, left, 
                                   right >>

PartitionLoop(self) == /\ pc[self] = "PartitionLoop"
                       /\ IF j[self] <= right_[self]
                             THEN /\ IF array[j[self]] < pivot[self]
                                        THEN /\ LET tmp == array[j[self]] IN
                                                  array' = [array EXCEPT ![j[self]] = array[i[self]],
                                                                         ![i[self]] = tmp]
                                             /\ i' = [i EXCEPT ![self] = i[self] + 1]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << array, i >>
                                  /\ j' = [j EXCEPT ![self] = j[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "PartitionLoop"]
                                  /\ UNCHANGED << mid, stack, left_, right_, 
                                                  pivot >>
                             ELSE /\ LET tmp == array[i[self]] IN
                                       array' = [array EXCEPT ![i[self]] = array[right_[self]],
                                                              ![right_[self]] = tmp]
                                  /\ mid' = i[self]
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ pivot' = [pivot EXCEPT ![self] = Head(stack[self]).pivot]
                                  /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                                  /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
                                  /\ left_' = [left_ EXCEPT ![self] = Head(stack[self]).left_]
                                  /\ right_' = [right_ EXCEPT ![self] = Head(stack[self]).right_]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << left, right >>

partition2(self) == Partition(self) \/ PartitionLoop(self)

QuickSort(self) == /\ pc[self] = "QuickSort"
                   /\ IF left[self] < right[self]
                         THEN /\ /\ left_' = [left_ EXCEPT ![self] = left[self]]
                                 /\ right_' = [right_ EXCEPT ![self] = right[self]]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "partition2",
                                                                          pc        |->  "SortLeft",
                                                                          pivot     |->  pivot[self],
                                                                          i         |->  i[self],
                                                                          j         |->  j[self],
                                                                          left_     |->  left_[self],
                                                                          right_    |->  right_[self] ] >>
                                                                      \o stack[self]]
                              /\ pivot' = [pivot EXCEPT ![self] = defaultInitValue]
                              /\ i' = [i EXCEPT ![self] = defaultInitValue]
                              /\ j' = [j EXCEPT ![self] = defaultInitValue]
                              /\ pc' = [pc EXCEPT ![self] = "Partition"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "CheckSubArraySorted"]
                              /\ UNCHANGED << stack, left_, right_, pivot, i, 
                                              j >>
                   /\ UNCHANGED << array, mid, left, right >>

SortLeft(self) == /\ pc[self] = "SortLeft"
                  /\ /\ left' = [left EXCEPT ![self] = left[self]]
                     /\ right' = [right EXCEPT ![self] = mid - 1]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sort",
                                                              pc        |->  "SortRight",
                                                              left      |->  left[self],
                                                              right     |->  right[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "QuickSort"]
                  /\ UNCHANGED << array, mid, left_, right_, pivot, i, j >>

SortRight(self) == /\ pc[self] = "SortRight"
                   /\ /\ left' = [left EXCEPT ![self] = mid + 1]
                      /\ right' = [right EXCEPT ![self] = right[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sort",
                                                               pc        |->  "CheckSubArraySorted",
                                                               left      |->  left[self],
                                                               right     |->  right[self] ] >>
                                                           \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "QuickSort"]
                   /\ UNCHANGED << array, mid, left_, right_, pivot, i, j >>

CheckSubArraySorted(self) == /\ pc[self] = "CheckSubArraySorted"
                             /\ Assert(Sorted(SubSeq(array, left[self], right[self])), 
                                       "Failure of assertion at line 67, column 9.")
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ left' = [left EXCEPT ![self] = Head(stack[self]).left]
                             /\ right' = [right EXCEPT ![self] = Head(stack[self]).right]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << array, mid, left_, right_, pivot, 
                                             i, j >>

sort(self) == QuickSort(self) \/ SortLeft(self) \/ SortRight(self)
                 \/ CheckSubArraySorted(self)

Main == /\ pc["main"] = "Main"
        /\ /\ left' = [left EXCEPT !["main"] = 1]
           /\ right' = [right EXCEPT !["main"] = Len(array)]
           /\ stack' = [stack EXCEPT !["main"] = << [ procedure |->  "sort",
                                                      pc        |->  "CheckSorted",
                                                      left      |->  left["main"],
                                                      right     |->  right["main"] ] >>
                                                  \o stack["main"]]
        /\ pc' = [pc EXCEPT !["main"] = "QuickSort"]
        /\ UNCHANGED << array, mid, left_, right_, pivot, i, j >>

CheckSorted == /\ pc["main"] = "CheckSorted"
               /\ Assert(Sorted(array), 
                         "Failure of assertion at line 76, column 9.")
               /\ pc' = [pc EXCEPT !["main"] = "Done"]
               /\ UNCHANGED << array, mid, stack, left_, right_, pivot, i, j, 
                               left, right >>

main == Main \/ CheckSorted

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: partition2(self) \/ sort(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

StackLenLimit == \A self \in ProcSet: Len(stack[self]) < 20

====
