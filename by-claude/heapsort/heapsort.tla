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

(*--fair algorithm heapsort
variables
    array \in PossibleInputs,
    i = 1,
    j = 1,
    parent = 1,
    child = 1,
    temp = 0,
    heapSize = Len(array);

procedure heapify(root, size)
variables
    largest = 1,
    left = 1,
    right = 1;
begin
    HeapifyStart:
        largest := root;
        left := 2 * root;
        right := 2 * root + 1;
        
    CheckLeft:
        if left <= size /\ array[left] > array[largest] then
            largest := left;
        end if;
        
    CheckRight:
        if right <= size /\ array[right] > array[largest] then
            largest := right;
        end if;
        
    SwapIfNeeded:
        if largest /= root then
            temp := array[root] ||
            array[root] := array[largest] ||
            array[largest] := array[root];
            call heapify(largest, size);
        end if;
        
    HeapifyReturn:
        return;
end procedure;

procedure buildMaxHeap()
begin
    BuildHeapStart:
        i := Len(array) \div 2;
        
    BuildHeapLoop:
        while i >= 1 do
            call heapify(i, Len(array));
        BuildHeapLoopEnd:
            i := i - 1;
        end while;
        
    BuildHeapReturn:
        return;
end procedure;

procedure sort()
begin
    StartHeapSort:
        call buildMaxHeap();
        
    HeapSortLoop:
        heapSize := Len(array);
        
    ExtractMax:
        while heapSize > 1 do
            temp := array[1] ||
            array[1] := array[heapSize] ||
            array[heapSize] := array[1];
            heapSize := heapSize - 1;
            call heapify(1, heapSize);
        end while;
        
    SortReturn:
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
\* BEGIN TRANSLATION (chksum(pcal) = "fdd66ec1" /\ chksum(tla) = "be567a2f")
CONSTANT defaultInitValue
VARIABLES array, i, j, parent, child, temp, heapSize, pc, stack, root, size, 
          largest, left, right

vars == << array, i, j, parent, child, temp, heapSize, pc, stack, root, size, 
           largest, left, right >>

ProcSet == {"main"}

Init == (* Global variables *)
        /\ array \in PossibleInputs
        /\ i = 1
        /\ j = 1
        /\ parent = 1
        /\ child = 1
        /\ temp = 0
        /\ heapSize = Len(array)
        (* Procedure heapify *)
        /\ root = [ self \in ProcSet |-> defaultInitValue]
        /\ size = [ self \in ProcSet |-> defaultInitValue]
        /\ largest = [ self \in ProcSet |-> 1]
        /\ left = [ self \in ProcSet |-> 1]
        /\ right = [ self \in ProcSet |-> 1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Main"]

HeapifyStart(self) == /\ pc[self] = "HeapifyStart"
                      /\ largest' = [largest EXCEPT ![self] = root[self]]
                      /\ left' = [left EXCEPT ![self] = 2 * root[self]]
                      /\ right' = [right EXCEPT ![self] = 2 * root[self] + 1]
                      /\ pc' = [pc EXCEPT ![self] = "CheckLeft"]
                      /\ UNCHANGED << array, i, j, parent, child, temp, 
                                      heapSize, stack, root, size >>

CheckLeft(self) == /\ pc[self] = "CheckLeft"
                   /\ IF left[self] <= size[self] /\ array[left[self]] > array[largest[self]]
                         THEN /\ largest' = [largest EXCEPT ![self] = left[self]]
                         ELSE /\ TRUE
                              /\ UNCHANGED largest
                   /\ pc' = [pc EXCEPT ![self] = "CheckRight"]
                   /\ UNCHANGED << array, i, j, parent, child, temp, heapSize, 
                                   stack, root, size, left, right >>

CheckRight(self) == /\ pc[self] = "CheckRight"
                    /\ IF right[self] <= size[self] /\ array[right[self]] > array[largest[self]]
                          THEN /\ largest' = [largest EXCEPT ![self] = right[self]]
                          ELSE /\ TRUE
                               /\ UNCHANGED largest
                    /\ pc' = [pc EXCEPT ![self] = "SwapIfNeeded"]
                    /\ UNCHANGED << array, i, j, parent, child, temp, heapSize, 
                                    stack, root, size, left, right >>

SwapIfNeeded(self) == /\ pc[self] = "SwapIfNeeded"
                      /\ IF largest[self] /= root[self]
                            THEN /\ /\ array' = [array EXCEPT ![root[self]] = array[largest[self]],
                                                              ![largest[self]] = array[root[self]]]
                                    /\ temp' = array[root[self]]
                                 /\ /\ root' = [root EXCEPT ![self] = largest[self]]
                                    /\ size' = [size EXCEPT ![self] = size[self]]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "heapify",
                                                                             pc        |->  "HeapifyReturn",
                                                                             largest   |->  largest[self],
                                                                             left      |->  left[self],
                                                                             right     |->  right[self],
                                                                             root      |->  root[self],
                                                                             size      |->  size[self] ] >>
                                                                         \o stack[self]]
                                 /\ largest' = [largest EXCEPT ![self] = 1]
                                 /\ left' = [left EXCEPT ![self] = 1]
                                 /\ right' = [right EXCEPT ![self] = 1]
                                 /\ pc' = [pc EXCEPT ![self] = "HeapifyStart"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "HeapifyReturn"]
                                 /\ UNCHANGED << array, temp, stack, root, 
                                                 size, largest, left, right >>
                      /\ UNCHANGED << i, j, parent, child, heapSize >>

HeapifyReturn(self) == /\ pc[self] = "HeapifyReturn"
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ largest' = [largest EXCEPT ![self] = Head(stack[self]).largest]
                       /\ left' = [left EXCEPT ![self] = Head(stack[self]).left]
                       /\ right' = [right EXCEPT ![self] = Head(stack[self]).right]
                       /\ root' = [root EXCEPT ![self] = Head(stack[self]).root]
                       /\ size' = [size EXCEPT ![self] = Head(stack[self]).size]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << array, i, j, parent, child, temp, 
                                       heapSize >>

heapify(self) == HeapifyStart(self) \/ CheckLeft(self) \/ CheckRight(self)
                    \/ SwapIfNeeded(self) \/ HeapifyReturn(self)

BuildHeapStart(self) == /\ pc[self] = "BuildHeapStart"
                        /\ i' = (Len(array) \div 2)
                        /\ pc' = [pc EXCEPT ![self] = "BuildHeapLoop"]
                        /\ UNCHANGED << array, j, parent, child, temp, 
                                        heapSize, stack, root, size, largest, 
                                        left, right >>

BuildHeapLoop(self) == /\ pc[self] = "BuildHeapLoop"
                       /\ IF i >= 1
                             THEN /\ /\ root' = [root EXCEPT ![self] = i]
                                     /\ size' = [size EXCEPT ![self] = Len(array)]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "heapify",
                                                                              pc        |->  "BuildHeapLoopEnd",
                                                                              largest   |->  largest[self],
                                                                              left      |->  left[self],
                                                                              right     |->  right[self],
                                                                              root      |->  root[self],
                                                                              size      |->  size[self] ] >>
                                                                          \o stack[self]]
                                  /\ largest' = [largest EXCEPT ![self] = 1]
                                  /\ left' = [left EXCEPT ![self] = 1]
                                  /\ right' = [right EXCEPT ![self] = 1]
                                  /\ pc' = [pc EXCEPT ![self] = "HeapifyStart"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "BuildHeapReturn"]
                                  /\ UNCHANGED << stack, root, size, largest, 
                                                  left, right >>
                       /\ UNCHANGED << array, i, j, parent, child, temp, 
                                       heapSize >>

BuildHeapLoopEnd(self) == /\ pc[self] = "BuildHeapLoopEnd"
                          /\ i' = i - 1
                          /\ pc' = [pc EXCEPT ![self] = "BuildHeapLoop"]
                          /\ UNCHANGED << array, j, parent, child, temp, 
                                          heapSize, stack, root, size, largest, 
                                          left, right >>

BuildHeapReturn(self) == /\ pc[self] = "BuildHeapReturn"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << array, i, j, parent, child, temp, 
                                         heapSize, root, size, largest, left, 
                                         right >>

buildMaxHeap(self) == BuildHeapStart(self) \/ BuildHeapLoop(self)
                         \/ BuildHeapLoopEnd(self) \/ BuildHeapReturn(self)

StartHeapSort(self) == /\ pc[self] = "StartHeapSort"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "buildMaxHeap",
                                                                pc        |->  "HeapSortLoop" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "BuildHeapStart"]
                       /\ UNCHANGED << array, i, j, parent, child, temp, 
                                       heapSize, root, size, largest, left, 
                                       right >>

HeapSortLoop(self) == /\ pc[self] = "HeapSortLoop"
                      /\ heapSize' = Len(array)
                      /\ pc' = [pc EXCEPT ![self] = "ExtractMax"]
                      /\ UNCHANGED << array, i, j, parent, child, temp, stack, 
                                      root, size, largest, left, right >>

ExtractMax(self) == /\ pc[self] = "ExtractMax"
                    /\ IF heapSize > 1
                          THEN /\ /\ array' = [array EXCEPT ![1] = array[heapSize],
                                                            ![heapSize] = array[1]]
                                  /\ temp' = array[1]
                               /\ heapSize' = heapSize - 1
                               /\ /\ root' = [root EXCEPT ![self] = 1]
                                  /\ size' = [size EXCEPT ![self] = heapSize']
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "heapify",
                                                                           pc        |->  "ExtractMax",
                                                                           largest   |->  largest[self],
                                                                           left      |->  left[self],
                                                                           right     |->  right[self],
                                                                           root      |->  root[self],
                                                                           size      |->  size[self] ] >>
                                                                       \o stack[self]]
                               /\ largest' = [largest EXCEPT ![self] = 1]
                               /\ left' = [left EXCEPT ![self] = 1]
                               /\ right' = [right EXCEPT ![self] = 1]
                               /\ pc' = [pc EXCEPT ![self] = "HeapifyStart"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "SortReturn"]
                               /\ UNCHANGED << array, temp, heapSize, stack, 
                                               root, size, largest, left, 
                                               right >>
                    /\ UNCHANGED << i, j, parent, child >>

SortReturn(self) == /\ pc[self] = "SortReturn"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << array, i, j, parent, child, temp, heapSize, 
                                    root, size, largest, left, right >>

sort(self) == StartHeapSort(self) \/ HeapSortLoop(self) \/ ExtractMax(self)
                 \/ SortReturn(self)

Main == /\ pc["main"] = "Main"
        /\ stack' = [stack EXCEPT !["main"] = << [ procedure |->  "sort",
                                                   pc        |->  "CheckSorted" ] >>
                                               \o stack["main"]]
        /\ pc' = [pc EXCEPT !["main"] = "StartHeapSort"]
        /\ UNCHANGED << array, i, j, parent, child, temp, heapSize, root, size, 
                        largest, left, right >>

CheckSorted == /\ pc["main"] = "CheckSorted"
               /\ Assert(Sorted(array), 
                         "Failure of assertion at line 99, column 9.")
               /\ pc' = [pc EXCEPT !["main"] = "Done"]
               /\ UNCHANGED << array, i, j, parent, child, temp, heapSize, 
                               stack, root, size, largest, left, right >>

main == Main \/ CheckSorted

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet:  \/ heapify(self) \/ buildMaxHeap(self)
                                     \/ sort(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


====
