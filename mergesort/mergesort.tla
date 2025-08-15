---- MODULE mergesort ----
EXTENDS TLC, Integers, Sequences

CONSTANTS 
    MaxArrayLength,
    Items

Sorted(array) ==
    \A i \in 1..Len(array)-1:
        array[i] <= array[i + 1]

PossibleInputs ==
    UNION {[1..n -> Items] : n \in 0..MaxArrayLength}

(*--fair algorithm mergesort
variables
    array \in PossibleInputs;

procedure merge(left, mid, right)
variables
    i = left,
    leftPart,
    rightPart;
begin
    Merge:
        assert left <= mid;
        assert mid + 1 <= right;

        leftPart := SubSeq(array, left, mid);
        rightPart := SubSeq(array, mid + 1, right);

        MergeLoop:
            while i <= right do
                if leftPart /= <<>> /\ rightPart /= <<>> then
                    with 
                        l = Head(leftPart),
                        r = Head(rightPart)
                    do
                        if l < r then
                            array[i] := l;
                            leftPart := Tail(leftPart);
                        else
                            array[i] := r;
                            rightPart := Tail(rightPart);
                        end if;
                    end with;
                elsif leftPart = <<>> then
                    array[i] := Head(rightPart);
                    rightPart := Tail(rightPart);
                else
                    assert rightPart = <<>>;
                    array[i] := Head(leftPart);
                    leftPart := Tail(leftPart);
                end if;
                i := i + 1;
            end while;
        return;
end procedure;

procedure sort(left, right)
variables
    mid;
begin
    Sort:
        if left >= right then
            return;
        else
            mid := (left + right) \div 2;
            SortLeft:
                call sort(left, mid);
            SortRight:
                call sort(mid + 1, right);
            MergeLeftAndRight:
                call merge(left, mid, right);
            CheckSubArraySorted:
                assert Sorted(SubSeq(array, left, right));
            return;
        end if;
end procedure;

process main = "main"
begin
    Main:
        call sort(1, Len(array));
    CheckSorted:
        assert Sorted(array);
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "1c10c6ca")
\* Procedure variable mid of procedure sort at line 65 col 5 changed to mid_
\* Parameter left of procedure merge at line 22 col 17 changed to left_
\* Parameter right of procedure merge at line 22 col 28 changed to right_
CONSTANT defaultInitValue
VARIABLES pc, array, stack, left_, mid, right_, i, leftPart, rightPart, left, 
          right, mid_

vars == << pc, array, stack, left_, mid, right_, i, leftPart, rightPart, left, 
           right, mid_ >>

ProcSet == {"main"}

Init == (* Global variables *)
        /\ array \in PossibleInputs
        (* Procedure merge *)
        /\ left_ = [ self \in ProcSet |-> defaultInitValue]
        /\ mid = [ self \in ProcSet |-> defaultInitValue]
        /\ right_ = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> left_[self]]
        /\ leftPart = [ self \in ProcSet |-> defaultInitValue]
        /\ rightPart = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure sort *)
        /\ left = [ self \in ProcSet |-> defaultInitValue]
        /\ right = [ self \in ProcSet |-> defaultInitValue]
        /\ mid_ = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Main"]

Merge(self) == /\ pc[self] = "Merge"
               /\ Assert(left_[self] <= mid[self], 
                         "Failure of assertion at line 29, column 9.")
               /\ Assert(mid[self] + 1 <= right_[self], 
                         "Failure of assertion at line 30, column 9.")
               /\ leftPart' = [leftPart EXCEPT ![self] = SubSeq(array, left_[self], mid[self])]
               /\ rightPart' = [rightPart EXCEPT ![self] = SubSeq(array, mid[self] + 1, right_[self])]
               /\ pc' = [pc EXCEPT ![self] = "MergeLoop"]
               /\ UNCHANGED << array, stack, left_, mid, right_, i, left, 
                               right, mid_ >>

MergeLoop(self) == /\ pc[self] = "MergeLoop"
                   /\ IF i[self] <= right_[self]
                         THEN /\ IF leftPart[self] /= <<>> /\ rightPart[self] /= <<>>
                                    THEN /\ LET l == Head(leftPart[self]) IN
                                              LET r == Head(rightPart[self]) IN
                                                IF l < r
                                                   THEN /\ array' = [array EXCEPT ![i[self]] = l]
                                                        /\ leftPart' = [leftPart EXCEPT ![self] = Tail(leftPart[self])]
                                                        /\ UNCHANGED rightPart
                                                   ELSE /\ array' = [array EXCEPT ![i[self]] = r]
                                                        /\ rightPart' = [rightPart EXCEPT ![self] = Tail(rightPart[self])]
                                                        /\ UNCHANGED leftPart
                                    ELSE /\ IF leftPart[self] = <<>>
                                               THEN /\ array' = [array EXCEPT ![i[self]] = Head(rightPart[self])]
                                                    /\ rightPart' = [rightPart EXCEPT ![self] = Tail(rightPart[self])]
                                                    /\ UNCHANGED leftPart
                                               ELSE /\ Assert(rightPart[self] = <<>>, 
                                                              "Failure of assertion at line 54, column 21.")
                                                    /\ array' = [array EXCEPT ![i[self]] = Head(leftPart[self])]
                                                    /\ leftPart' = [leftPart EXCEPT ![self] = Tail(leftPart[self])]
                                                    /\ UNCHANGED rightPart
                              /\ i' = [i EXCEPT ![self] = i[self] + 1]
                              /\ pc' = [pc EXCEPT ![self] = "MergeLoop"]
                              /\ UNCHANGED << stack, left_, mid, right_ >>
                         ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                              /\ leftPart' = [leftPart EXCEPT ![self] = Head(stack[self]).leftPart]
                              /\ rightPart' = [rightPart EXCEPT ![self] = Head(stack[self]).rightPart]
                              /\ left_' = [left_ EXCEPT ![self] = Head(stack[self]).left_]
                              /\ mid' = [mid EXCEPT ![self] = Head(stack[self]).mid]
                              /\ right_' = [right_ EXCEPT ![self] = Head(stack[self]).right_]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ array' = array
                   /\ UNCHANGED << left, right, mid_ >>

merge(self) == Merge(self) \/ MergeLoop(self)

Sort(self) == /\ pc[self] = "Sort"
              /\ IF left[self] >= right[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ mid_' = [mid_ EXCEPT ![self] = Head(stack[self]).mid_]
                         /\ left' = [left EXCEPT ![self] = Head(stack[self]).left]
                         /\ right' = [right EXCEPT ![self] = Head(stack[self]).right]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ mid_' = [mid_ EXCEPT ![self] = (left[self] + right[self]) \div 2]
                         /\ pc' = [pc EXCEPT ![self] = "SortLeft"]
                         /\ UNCHANGED << stack, left, right >>
              /\ UNCHANGED << array, left_, mid, right_, i, leftPart, 
                              rightPart >>

SortLeft(self) == /\ pc[self] = "SortLeft"
                  /\ /\ left' = [left EXCEPT ![self] = left[self]]
                     /\ right' = [right EXCEPT ![self] = mid_[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sort",
                                                              pc        |->  "SortRight",
                                                              mid_      |->  mid_[self],
                                                              left      |->  left[self],
                                                              right     |->  right[self] ] >>
                                                          \o stack[self]]
                  /\ mid_' = [mid_ EXCEPT ![self] = defaultInitValue]
                  /\ pc' = [pc EXCEPT ![self] = "Sort"]
                  /\ UNCHANGED << array, left_, mid, right_, i, leftPart, 
                                  rightPart >>

SortRight(self) == /\ pc[self] = "SortRight"
                   /\ /\ left' = [left EXCEPT ![self] = mid_[self] + 1]
                      /\ right' = [right EXCEPT ![self] = right[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sort",
                                                               pc        |->  "MergeLeftAndRight",
                                                               mid_      |->  mid_[self],
                                                               left      |->  left[self],
                                                               right     |->  right[self] ] >>
                                                           \o stack[self]]
                   /\ mid_' = [mid_ EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "Sort"]
                   /\ UNCHANGED << array, left_, mid, right_, i, leftPart, 
                                   rightPart >>

MergeLeftAndRight(self) == /\ pc[self] = "MergeLeftAndRight"
                           /\ /\ left_' = [left_ EXCEPT ![self] = left[self]]
                              /\ mid' = [mid EXCEPT ![self] = mid_[self]]
                              /\ right_' = [right_ EXCEPT ![self] = right[self]]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "merge",
                                                                       pc        |->  "CheckSubArraySorted",
                                                                       i         |->  i[self],
                                                                       leftPart  |->  leftPart[self],
                                                                       rightPart |->  rightPart[self],
                                                                       left_     |->  left_[self],
                                                                       mid       |->  mid[self],
                                                                       right_    |->  right_[self] ] >>
                                                                   \o stack[self]]
                           /\ i' = [i EXCEPT ![self] = left_'[self]]
                           /\ leftPart' = [leftPart EXCEPT ![self] = defaultInitValue]
                           /\ rightPart' = [rightPart EXCEPT ![self] = defaultInitValue]
                           /\ pc' = [pc EXCEPT ![self] = "Merge"]
                           /\ UNCHANGED << array, left, right, mid_ >>

CheckSubArraySorted(self) == /\ pc[self] = "CheckSubArraySorted"
                             /\ Assert(Sorted(SubSeq(array, left[self], right[self])), 
                                       "Failure of assertion at line 79, column 17.")
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ mid_' = [mid_ EXCEPT ![self] = Head(stack[self]).mid_]
                             /\ left' = [left EXCEPT ![self] = Head(stack[self]).left]
                             /\ right' = [right EXCEPT ![self] = Head(stack[self]).right]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << array, left_, mid, right_, i, 
                                             leftPart, rightPart >>

sort(self) == Sort(self) \/ SortLeft(self) \/ SortRight(self)
                 \/ MergeLeftAndRight(self) \/ CheckSubArraySorted(self)

Main == /\ pc["main"] = "Main"
        /\ /\ left' = [left EXCEPT !["main"] = 1]
           /\ right' = [right EXCEPT !["main"] = Len(array)]
           /\ stack' = [stack EXCEPT !["main"] = << [ procedure |->  "sort",
                                                      pc        |->  "CheckSorted",
                                                      mid_      |->  mid_["main"],
                                                      left      |->  left["main"],
                                                      right     |->  right["main"] ] >>
                                                  \o stack["main"]]
        /\ mid_' = [mid_ EXCEPT !["main"] = defaultInitValue]
        /\ pc' = [pc EXCEPT !["main"] = "Sort"]
        /\ UNCHANGED << array, left_, mid, right_, i, leftPart, rightPart >>

CheckSorted == /\ pc["main"] = "CheckSorted"
               /\ Assert(Sorted(array), 
                         "Failure of assertion at line 89, column 9.")
               /\ pc' = [pc EXCEPT !["main"] = "Done"]
               /\ UNCHANGED << array, stack, left_, mid, right_, i, leftPart, 
                               rightPart, left, right, mid_ >>

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

StackLenInvariant ==
    \A self \in ProcSet: Len(stack[self]) < 100

====
