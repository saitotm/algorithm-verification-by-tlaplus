---- MODULE quicksort ----
EXTENDS TLC, Integers, Sequences 

CONSTANTS 
    MaxArrayLength,
    Items

Sorted(array, low, high) ==
    \A i, j \in low..high:
        i < j => array[i] <= array[j]

PossibleInputs ==
    UNION {[1..n -> Items]: n \in 1..MaxArrayLength}

(*--fair algorithm quicksort
variables
    array \in PossibleInputs;

procedure quickSort(left, right)
variables
    pivot = 0,
    i = 0,
    j = 0,
    temp = 0;
begin
    QSCheck:
        if left < right then
            QSPartition:
                pivot := array[right];
                i := left - 1;
                j := left;
            
            QSLoop:
                while j < right do
                    QSCompare:
                        if array[j] <= pivot then
                            QSSwap:
                                i := i + 1;
                            QSSwapTemp:
                                temp := array[i];
                            QSSwapArray1:
                                array[i] := array[j];
                            QSSwapArray2:
                                array[j] := temp;
                        end if;
                    QSIncrement:
                        j := j + 1;
                end while;
                
            QSPivotSwap:
                i := i + 1;
            QSPivotSwapTemp:
                temp := array[i];
            QSPivotSwapArray1:
                array[i] := array[right];
            QSPivotSwapArray2:
                array[right] := temp;
                
            QSRecurseLeft:
                call quickSort(left, i - 1);
                
            QSRecurseRight:
                call quickSort(i + 1, right);
        end if;
    QSReturn:
        assert left > right \/ Sorted(array, left, right);
        return;
end procedure;

procedure sort()
begin
    StartQuickSort:
        if Len(array) > 0 then
            call quickSort(1, Len(array));
        end if;
    SortReturn:
        return;
end procedure;

process main = "main"
begin
    Main:
        call sort();
    CheckSorted:
        assert Len(array) = 0 \/ Sorted(array, 1, Len(array));
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "25d4369e")
CONSTANT defaultInitValue
VARIABLES pc, array, stack, left, right, pivot, i, j, temp

vars == << pc, array, stack, left, right, pivot, i, j, temp >>

ProcSet == {"main"}

Init == (* Global variables *)
        /\ array \in PossibleInputs
        (* Procedure quickSort *)
        /\ left = [ self \in ProcSet |-> defaultInitValue]
        /\ right = [ self \in ProcSet |-> defaultInitValue]
        /\ pivot = [ self \in ProcSet |-> 0]
        /\ i = [ self \in ProcSet |-> 0]
        /\ j = [ self \in ProcSet |-> 0]
        /\ temp = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Main"]

QSCheck(self) == /\ pc[self] = "QSCheck"
                 /\ IF left[self] < right[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "QSPartition"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "QSReturn"]
                 /\ UNCHANGED << array, stack, left, right, pivot, i, j, temp >>

QSPartition(self) == /\ pc[self] = "QSPartition"
                     /\ pivot' = [pivot EXCEPT ![self] = array[right[self]]]
                     /\ i' = [i EXCEPT ![self] = left[self] - 1]
                     /\ j' = [j EXCEPT ![self] = left[self]]
                     /\ pc' = [pc EXCEPT ![self] = "QSLoop"]
                     /\ UNCHANGED << array, stack, left, right, temp >>

QSLoop(self) == /\ pc[self] = "QSLoop"
                /\ IF j[self] < right[self]
                      THEN /\ pc' = [pc EXCEPT ![self] = "QSCompare"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "QSPivotSwap"]
                /\ UNCHANGED << array, stack, left, right, pivot, i, j, temp >>

QSCompare(self) == /\ pc[self] = "QSCompare"
                   /\ IF array[j[self]] <= pivot[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "QSSwap"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "QSIncrement"]
                   /\ UNCHANGED << array, stack, left, right, pivot, i, j, 
                                   temp >>

QSSwap(self) == /\ pc[self] = "QSSwap"
                /\ i' = [i EXCEPT ![self] = i[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "QSSwapTemp"]
                /\ UNCHANGED << array, stack, left, right, pivot, j, temp >>

QSSwapTemp(self) == /\ pc[self] = "QSSwapTemp"
                    /\ temp' = [temp EXCEPT ![self] = array[i[self]]]
                    /\ pc' = [pc EXCEPT ![self] = "QSSwapArray1"]
                    /\ UNCHANGED << array, stack, left, right, pivot, i, j >>

QSSwapArray1(self) == /\ pc[self] = "QSSwapArray1"
                      /\ array' = [array EXCEPT ![i[self]] = array[j[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "QSSwapArray2"]
                      /\ UNCHANGED << stack, left, right, pivot, i, j, temp >>

QSSwapArray2(self) == /\ pc[self] = "QSSwapArray2"
                      /\ array' = [array EXCEPT ![j[self]] = temp[self]]
                      /\ pc' = [pc EXCEPT ![self] = "QSIncrement"]
                      /\ UNCHANGED << stack, left, right, pivot, i, j, temp >>

QSIncrement(self) == /\ pc[self] = "QSIncrement"
                     /\ j' = [j EXCEPT ![self] = j[self] + 1]
                     /\ pc' = [pc EXCEPT ![self] = "QSLoop"]
                     /\ UNCHANGED << array, stack, left, right, pivot, i, temp >>

QSPivotSwap(self) == /\ pc[self] = "QSPivotSwap"
                     /\ i' = [i EXCEPT ![self] = i[self] + 1]
                     /\ pc' = [pc EXCEPT ![self] = "QSPivotSwapTemp"]
                     /\ UNCHANGED << array, stack, left, right, pivot, j, temp >>

QSPivotSwapTemp(self) == /\ pc[self] = "QSPivotSwapTemp"
                         /\ temp' = [temp EXCEPT ![self] = array[i[self]]]
                         /\ pc' = [pc EXCEPT ![self] = "QSPivotSwapArray1"]
                         /\ UNCHANGED << array, stack, left, right, pivot, i, 
                                         j >>

QSPivotSwapArray1(self) == /\ pc[self] = "QSPivotSwapArray1"
                           /\ array' = [array EXCEPT ![i[self]] = array[right[self]]]
                           /\ pc' = [pc EXCEPT ![self] = "QSPivotSwapArray2"]
                           /\ UNCHANGED << stack, left, right, pivot, i, j, 
                                           temp >>

QSPivotSwapArray2(self) == /\ pc[self] = "QSPivotSwapArray2"
                           /\ array' = [array EXCEPT ![right[self]] = temp[self]]
                           /\ pc' = [pc EXCEPT ![self] = "QSRecurseLeft"]
                           /\ UNCHANGED << stack, left, right, pivot, i, j, 
                                           temp >>

QSRecurseLeft(self) == /\ pc[self] = "QSRecurseLeft"
                       /\ /\ left' = [left EXCEPT ![self] = left[self]]
                          /\ right' = [right EXCEPT ![self] = i[self] - 1]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "quickSort",
                                                                   pc        |->  "QSRecurseRight",
                                                                   pivot     |->  pivot[self],
                                                                   i         |->  i[self],
                                                                   j         |->  j[self],
                                                                   temp      |->  temp[self],
                                                                   left      |->  left[self],
                                                                   right     |->  right[self] ] >>
                                                               \o stack[self]]
                       /\ pivot' = [pivot EXCEPT ![self] = 0]
                       /\ i' = [i EXCEPT ![self] = 0]
                       /\ j' = [j EXCEPT ![self] = 0]
                       /\ temp' = [temp EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "QSCheck"]
                       /\ array' = array

QSRecurseRight(self) == /\ pc[self] = "QSRecurseRight"
                        /\ /\ left' = [left EXCEPT ![self] = i[self] + 1]
                           /\ right' = [right EXCEPT ![self] = right[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "quickSort",
                                                                    pc        |->  "QSReturn",
                                                                    pivot     |->  pivot[self],
                                                                    i         |->  i[self],
                                                                    j         |->  j[self],
                                                                    temp      |->  temp[self],
                                                                    left      |->  left[self],
                                                                    right     |->  right[self] ] >>
                                                                \o stack[self]]
                        /\ pivot' = [pivot EXCEPT ![self] = 0]
                        /\ i' = [i EXCEPT ![self] = 0]
                        /\ j' = [j EXCEPT ![self] = 0]
                        /\ temp' = [temp EXCEPT ![self] = 0]
                        /\ pc' = [pc EXCEPT ![self] = "QSCheck"]
                        /\ array' = array

QSReturn(self) == /\ pc[self] = "QSReturn"
                  /\ Assert(left[self] > right[self] \/ Sorted(array, left[self], right[self]), 
                            "Failure of assertion at line 66, column 9.")
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ pivot' = [pivot EXCEPT ![self] = Head(stack[self]).pivot]
                  /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                  /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
                  /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
                  /\ left' = [left EXCEPT ![self] = Head(stack[self]).left]
                  /\ right' = [right EXCEPT ![self] = Head(stack[self]).right]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ array' = array

quickSort(self) == QSCheck(self) \/ QSPartition(self) \/ QSLoop(self)
                      \/ QSCompare(self) \/ QSSwap(self)
                      \/ QSSwapTemp(self) \/ QSSwapArray1(self)
                      \/ QSSwapArray2(self) \/ QSIncrement(self)
                      \/ QSPivotSwap(self) \/ QSPivotSwapTemp(self)
                      \/ QSPivotSwapArray1(self) \/ QSPivotSwapArray2(self)
                      \/ QSRecurseLeft(self) \/ QSRecurseRight(self)
                      \/ QSReturn(self)

StartQuickSort(self) == /\ pc[self] = "StartQuickSort"
                        /\ IF Len(array) > 0
                              THEN /\ /\ left' = [left EXCEPT ![self] = 1]
                                      /\ right' = [right EXCEPT ![self] = Len(array)]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "quickSort",
                                                                               pc        |->  "SortReturn",
                                                                               pivot     |->  pivot[self],
                                                                               i         |->  i[self],
                                                                               j         |->  j[self],
                                                                               temp      |->  temp[self],
                                                                               left      |->  left[self],
                                                                               right     |->  right[self] ] >>
                                                                           \o stack[self]]
                                   /\ pivot' = [pivot EXCEPT ![self] = 0]
                                   /\ i' = [i EXCEPT ![self] = 0]
                                   /\ j' = [j EXCEPT ![self] = 0]
                                   /\ temp' = [temp EXCEPT ![self] = 0]
                                   /\ pc' = [pc EXCEPT ![self] = "QSCheck"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "SortReturn"]
                                   /\ UNCHANGED << stack, left, right, pivot, 
                                                   i, j, temp >>
                        /\ array' = array

SortReturn(self) == /\ pc[self] = "SortReturn"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << array, left, right, pivot, i, j, temp >>

sort(self) == StartQuickSort(self) \/ SortReturn(self)

Main == /\ pc["main"] = "Main"
        /\ stack' = [stack EXCEPT !["main"] = << [ procedure |->  "sort",
                                                   pc        |->  "CheckSorted" ] >>
                                               \o stack["main"]]
        /\ pc' = [pc EXCEPT !["main"] = "StartQuickSort"]
        /\ UNCHANGED << array, left, right, pivot, i, j, temp >>

CheckSorted == /\ pc["main"] = "CheckSorted"
               /\ Assert(Len(array) = 0 \/ Sorted(array, 1, Len(array)), 
                         "Failure of assertion at line 85, column 9.")
               /\ pc' = [pc EXCEPT !["main"] = "Done"]
               /\ UNCHANGED << array, stack, left, right, pivot, i, j, temp >>

main == Main \/ CheckSorted

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: quickSort(self) \/ sort(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
