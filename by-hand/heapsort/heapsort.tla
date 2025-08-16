---- MODULE heapsort ----
EXTENDS TLC, Integers, Sequences
CONSTANTS 
    MaxArrayLength,
    Items

PossibleInputs ==
    UNION {[1..n -> Items] : n \in 1..MaxArrayLength}

Sorted(array) ==
    \A i, j \in 1..Len(array)
        : i < j => array[i] <= array[j]

RECURSIVE IsHeap(_, _, _)

IsHeap(array, size, root) ==
    LET 
        left == 2 * root + 1
        right == 2 * root + 2
    IN
        /\ (left < size =>
            /\ array[root + 1] >= array[left + 1]
            /\ IsHeap(array, size, left))
        /\ (right < size =>
            /\ array[root + 1] >= array[right + 1]
            /\ IsHeap(array, size, right))

(*--fair algorithm heapsort
variables
    array \in PossibleInputs;

macro swap(i, j) begin
    with tmp = array[i] do
        array[i] := array[j] ||
        array[j] := tmp;
    end with;
end macro;

procedure heapify(size, root)
variables
    largest,
    left,
    right;
begin
    StartHeapify:
        largest := root;
        left := 2 * root + 1;
        right := 2 * root + 2;

        assert 0 <= root /\ root < Len(array);
        assert 1 <= size /\ size <= Len(array);
        assert IsHeap(array, size, left);
        assert IsHeap(array, size, right);

    UpdateLargestByLeft:
        if 
            /\ left < size
            /\ array[left + 1] > array[largest + 1]
        then 
            largest := left;
        end if;

    UpdateLargestByRight:
        if 
            /\ right < size
            /\ array[right + 1] > array[largest + 1]
        then
            largest := right;
        end if;

        if largest /= root then
            swap(root + 1, largest + 1);
            CallHeapify:
                call heapify(size, largest);
        end if;

    FinishHeapify:
        assert IsHeap(array, size, root);
        return;
end procedure;

procedure sort()
variables
    size,
    i;
begin
    HeapSort:
        size := Len(array);
        i := size \div 2 - 1;
    BuildHeap:
        while i >= 0 do
            call heapify(size, i);
            DecrementI1:
                i := i - 1;
        end while;

        i := size - 1;
    Sort:
        while i > 0 do
            swap(1, i + 1);
            call heapify(i, 0);
            DecrementI2:
                i := i - 1;
        end while;
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
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "ca36b779")
\* Procedure variable size of procedure sort at line 84 col 5 changed to size_
CONSTANT defaultInitValue
VARIABLES pc, array, stack, size, root, largest, left, right, size_, i

vars == << pc, array, stack, size, root, largest, left, right, size_, i >>

ProcSet == {"main"}

Init == (* Global variables *)
        /\ array \in PossibleInputs
        (* Procedure heapify *)
        /\ size = [ self \in ProcSet |-> defaultInitValue]
        /\ root = [ self \in ProcSet |-> defaultInitValue]
        /\ largest = [ self \in ProcSet |-> defaultInitValue]
        /\ left = [ self \in ProcSet |-> defaultInitValue]
        /\ right = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure sort *)
        /\ size_ = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Main"]

StartHeapify(self) == /\ pc[self] = "StartHeapify"
                      /\ largest' = [largest EXCEPT ![self] = root[self]]
                      /\ left' = [left EXCEPT ![self] = 2 * root[self] + 1]
                      /\ right' = [right EXCEPT ![self] = 2 * root[self] + 2]
                      /\ Assert(0 <= root[self] /\ root[self] < Len(array), 
                                "Failure of assertion at line 50, column 9.")
                      /\ Assert(1 <= size[self] /\ size[self] <= Len(array), 
                                "Failure of assertion at line 51, column 9.")
                      /\ Assert(IsHeap(array, size[self], left'[self]), 
                                "Failure of assertion at line 52, column 9.")
                      /\ Assert(IsHeap(array, size[self], right'[self]), 
                                "Failure of assertion at line 53, column 9.")
                      /\ pc' = [pc EXCEPT ![self] = "UpdateLargestByLeft"]
                      /\ UNCHANGED << array, stack, size, root, size_, i >>

UpdateLargestByLeft(self) == /\ pc[self] = "UpdateLargestByLeft"
                             /\ IF /\ left[self] < size[self]
                                   /\ array[left[self] + 1] > array[largest[self] + 1]
                                   THEN /\ largest' = [largest EXCEPT ![self] = left[self]]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED largest
                             /\ pc' = [pc EXCEPT ![self] = "UpdateLargestByRight"]
                             /\ UNCHANGED << array, stack, size, root, left, 
                                             right, size_, i >>

UpdateLargestByRight(self) == /\ pc[self] = "UpdateLargestByRight"
                              /\ IF /\ right[self] < size[self]
                                    /\ array[right[self] + 1] > array[largest[self] + 1]
                                    THEN /\ largest' = [largest EXCEPT ![self] = right[self]]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED largest
                              /\ IF largest'[self] /= root[self]
                                    THEN /\ LET tmp == array[(root[self] + 1)] IN
                                              array' = [array EXCEPT ![(root[self] + 1)] = array[(largest'[self] + 1)],
                                                                     ![(largest'[self] + 1)] = tmp]
                                         /\ pc' = [pc EXCEPT ![self] = "CallHeapify"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "FinishHeapify"]
                                         /\ array' = array
                              /\ UNCHANGED << stack, size, root, left, right, 
                                              size_, i >>

CallHeapify(self) == /\ pc[self] = "CallHeapify"
                     /\ /\ root' = [root EXCEPT ![self] = largest[self]]
                        /\ size' = [size EXCEPT ![self] = size[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "heapify",
                                                                 pc        |->  "FinishHeapify",
                                                                 largest   |->  largest[self],
                                                                 left      |->  left[self],
                                                                 right     |->  right[self],
                                                                 size      |->  size[self],
                                                                 root      |->  root[self] ] >>
                                                             \o stack[self]]
                     /\ largest' = [largest EXCEPT ![self] = defaultInitValue]
                     /\ left' = [left EXCEPT ![self] = defaultInitValue]
                     /\ right' = [right EXCEPT ![self] = defaultInitValue]
                     /\ pc' = [pc EXCEPT ![self] = "StartHeapify"]
                     /\ UNCHANGED << array, size_, i >>

FinishHeapify(self) == /\ pc[self] = "FinishHeapify"
                       /\ Assert(IsHeap(array, size[self], root[self]), 
                                 "Failure of assertion at line 78, column 9.")
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ largest' = [largest EXCEPT ![self] = Head(stack[self]).largest]
                       /\ left' = [left EXCEPT ![self] = Head(stack[self]).left]
                       /\ right' = [right EXCEPT ![self] = Head(stack[self]).right]
                       /\ size' = [size EXCEPT ![self] = Head(stack[self]).size]
                       /\ root' = [root EXCEPT ![self] = Head(stack[self]).root]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << array, size_, i >>

heapify(self) == StartHeapify(self) \/ UpdateLargestByLeft(self)
                    \/ UpdateLargestByRight(self) \/ CallHeapify(self)
                    \/ FinishHeapify(self)

HeapSort(self) == /\ pc[self] = "HeapSort"
                  /\ size_' = [size_ EXCEPT ![self] = Len(array)]
                  /\ i' = [i EXCEPT ![self] = size_'[self] \div 2 - 1]
                  /\ pc' = [pc EXCEPT ![self] = "BuildHeap"]
                  /\ UNCHANGED << array, stack, size, root, largest, left, 
                                  right >>

BuildHeap(self) == /\ pc[self] = "BuildHeap"
                   /\ IF i[self] >= 0
                         THEN /\ /\ root' = [root EXCEPT ![self] = i[self]]
                                 /\ size' = [size EXCEPT ![self] = size_[self]]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "heapify",
                                                                          pc        |->  "DecrementI1",
                                                                          largest   |->  largest[self],
                                                                          left      |->  left[self],
                                                                          right     |->  right[self],
                                                                          size      |->  size[self],
                                                                          root      |->  root[self] ] >>
                                                                      \o stack[self]]
                              /\ largest' = [largest EXCEPT ![self] = defaultInitValue]
                              /\ left' = [left EXCEPT ![self] = defaultInitValue]
                              /\ right' = [right EXCEPT ![self] = defaultInitValue]
                              /\ pc' = [pc EXCEPT ![self] = "StartHeapify"]
                              /\ i' = i
                         ELSE /\ i' = [i EXCEPT ![self] = size_[self] - 1]
                              /\ pc' = [pc EXCEPT ![self] = "Sort"]
                              /\ UNCHANGED << stack, size, root, largest, left, 
                                              right >>
                   /\ UNCHANGED << array, size_ >>

DecrementI1(self) == /\ pc[self] = "DecrementI1"
                     /\ i' = [i EXCEPT ![self] = i[self] - 1]
                     /\ pc' = [pc EXCEPT ![self] = "BuildHeap"]
                     /\ UNCHANGED << array, stack, size, root, largest, left, 
                                     right, size_ >>

Sort(self) == /\ pc[self] = "Sort"
              /\ IF i[self] > 0
                    THEN /\ LET tmp == array[1] IN
                              array' = [array EXCEPT ![1] = array[(i[self] + 1)],
                                                     ![(i[self] + 1)] = tmp]
                         /\ /\ root' = [root EXCEPT ![self] = 0]
                            /\ size' = [size EXCEPT ![self] = i[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "heapify",
                                                                     pc        |->  "DecrementI2",
                                                                     largest   |->  largest[self],
                                                                     left      |->  left[self],
                                                                     right     |->  right[self],
                                                                     size      |->  size[self],
                                                                     root      |->  root[self] ] >>
                                                                 \o stack[self]]
                         /\ largest' = [largest EXCEPT ![self] = defaultInitValue]
                         /\ left' = [left EXCEPT ![self] = defaultInitValue]
                         /\ right' = [right EXCEPT ![self] = defaultInitValue]
                         /\ pc' = [pc EXCEPT ![self] = "StartHeapify"]
                         /\ UNCHANGED << size_, i >>
                    ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ size_' = [size_ EXCEPT ![self] = Head(stack[self]).size_]
                         /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << array, size, root, largest, left, 
                                         right >>

DecrementI2(self) == /\ pc[self] = "DecrementI2"
                     /\ i' = [i EXCEPT ![self] = i[self] - 1]
                     /\ pc' = [pc EXCEPT ![self] = "Sort"]
                     /\ UNCHANGED << array, stack, size, root, largest, left, 
                                     right, size_ >>

sort(self) == HeapSort(self) \/ BuildHeap(self) \/ DecrementI1(self)
                 \/ Sort(self) \/ DecrementI2(self)

Main == /\ pc["main"] = "Main"
        /\ stack' = [stack EXCEPT !["main"] = << [ procedure |->  "sort",
                                                   pc        |->  "CheckSorted",
                                                   size_     |->  size_["main"],
                                                   i         |->  i["main"] ] >>
                                               \o stack["main"]]
        /\ size_' = [size_ EXCEPT !["main"] = defaultInitValue]
        /\ i' = [i EXCEPT !["main"] = defaultInitValue]
        /\ pc' = [pc EXCEPT !["main"] = "HeapSort"]
        /\ UNCHANGED << array, size, root, largest, left, right >>

CheckSorted == /\ pc["main"] = "CheckSorted"
               /\ Assert(Sorted(array), 
                         "Failure of assertion at line 113, column 9.")
               /\ pc' = [pc EXCEPT !["main"] = "Done"]
               /\ UNCHANGED << array, stack, size, root, largest, left, right, 
                               size_, i >>

main == Main \/ CheckSorted

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: heapify(self) \/ sort(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


====
