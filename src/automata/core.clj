(ns automata.core
  (:require reduce-fsm
            [automat.core :as auto]
            [automat.fsm :as fsm]
            [automat.viz :refer [view save]]
            [clojure.math.combinatorics :as comb]
            [instaparse.core :as insta])
  (:use clojure.test))

; The classic interview problem

(defn maximum-segment-sum [s]
  (let [step (fn [segment-sum n] (max 0 (+ segment-sum n)))]
    (apply max (reductions step 0 s))))

; But we're going to do something trickier, we're looking for the maximum sum
; among subsequences that are *not* a continguous segment.

; In theory we could do something like this:
;(defn maximum-non-segment-sum [s]
;  (->> (all-non-segment-subsequences s)
;    (map (partial apply +))
;    (apply max)))

; But how to write all-non-segment-subsequences ?

; First key insight is that you can represent a subsequence by applying a bitmask
; of 0s and 1s to the sequence.

(defn apply-bitmask
  "Takes a sequence and a bitmask, and returns the correpsonding subsequence"
  [s bitmask]
  (for [[item bit] (map vector s bitmask) :when (= bit 1)] item))

(deftest apply-bitmask-test
  (is (= [2 3 5] (apply-bitmask [1 2 3 4 5] [0 1 1 0 1]))))

; We can describe the satisfactory bitmasks with a regex 
; Regex "0* 1+ 0+ 1 (0|1)*" recognizes whether bitmask represents a non-segment

; All regexes have a corresponding automaton.  
; The automat library lets us easily build an automaton from a regex.

(def non-segment-automaton
  (auto/compile
    [(auto/* 0) (auto/+ 1) (auto/+ 0) 1 (auto/* (auto/or 0 1))]))

; We use an automaton by making repeated calls to auto/advance.
; auto/advance takes an initial value (not relevant here) 
; or the outputted state from a previous call to auto/advance
; so it works well with Clojure's reduce.

;=> (auto/advance non-segment-automaton nil 0)
;#automat.core.CompiledAutomatonState{:accepted? false, :checkpoint nil, :state-index 0, :start-index 0, :stream-index 1, :value nil}
;=> (auto/advance non-segment-automaton *1 1)
;#automat.core.CompiledAutomatonState{:accepted? false, :checkpoint nil, :state-index 1, :start-index 0, :stream-index 2, :value nil}
;=> (auto/advance non-segment-automaton *1 0)
;#automat.core.CompiledAutomatonState{:accepted? false, :checkpoint nil, :state-index 2, :start-index 0, :stream-index 3, :value nil}
;=> (auto/advance non-segment-automaton *1 1)
;#automat.core.CompiledAutomatonState{:accepted? true, :checkpoint nil, :state-index 3, :start-index 0, :stream-index 4, :value nil}

(defn non-segment-bitmask?
  "Takes a sequence of 0's and 1's and determines whether this represents
   a subsequence that is not a contiguous segment"
  [s]
  (get (reduce (partial auto/advance non-segment-automaton) nil s) :accepted? false))

(deftest non-segment-bitmask?-test
  (is (= true  (non-segment-bitmask? [0 1 1 0 1]))) 
  (is (= false (non-segment-bitmask? [0 1 1 0])))
  (is (= false (non-segment-bitmask? [0 0])))
  (is (= false (non-segment-bitmask? [])))
  (is (= false (non-segment-bitmask? [1]))))


(defn all-non-segment-subsequences
  "Takes a sequence and returns all subsequences that are not a contiguous segment"
  [s]
  (->> (apply comb/cartesian-product (repeat (count s) [0 1])) ; all bitmasks
    (filter non-segment-bitmask?)
    (map (partial apply-bitmask s))))

(deftest all-non-segment-subsequences-test
  (is (= '((2 4) (1 4) (1 3) (1 3 4) (1 2 4))
         (all-non-segment-subsequences [1 2 3 4])))
  
  (is (= '((3 5) (2 5) (2 4) (2 4 5) (2 3 5) (1 5) (1 4) (1 4 5) (1 3) (1 3 5) 
           (1 3 4) (1 3 4 5) (1 2 5) (1 2 4) (1 2 4 5) (1 2 3 5))
         (all-non-segment-subsequences [1 2 3 4 5]))))
         

(defn maximum-non-segment-sum-slow-version [s]
  (->> (all-non-segment-subsequences s)
    (map (partial apply +))
    (apply max)))

; The problem with the above version is that it is O(2^n)
; We can get this down to O(n) by cleverly interleaving the 
; automaton constraint checking with the summing/max process.
; As we do one pass through the sequence, our accumulator
; tracks the maximum sum we can get ending in a given state of our state machine.
; At the end of the pass, the value associated with the accepting state is our answer.

; Getting at the individual states and transitions of the automaton produced by automat
; is tricky, so for clarity, I've implemented this next function by simply
; encoding the states and transitions directly with Clojure maps 
; (where states are keywords, transitions are numbers 0 or 1)
; Next, I'll show how to do this more generally in automat.

(defn maximum-non-segment-sum [s]
  (let [transitions {:s0 {0 :s0, 1 :s1},
                     :s1 {0 :s2, 1 :s1},
                     :s2 {0 :s2, 1 :s3},
                     :s3 {0 :s3, 1 :s3}},
        
        step-state-sum-map     ; the reducing function
        (fn [state-sum-map n]
          (apply merge-with max
                 (mapcat (fn [[state sum]] [{((transitions state) 0) sum}
                                            {((transitions state) 1) (+ sum n)}])
                         state-sum-map)))]
    
  (get (reduce step-state-sum-map {:s0 0} s) :s3)))

; Now for the grand finale, we want to find the maximum-sum from an arbitrary bitmask regex
; Using instaparse in conjunction with the automat library, 
; we can turn a bitmask regex into an automaton

(def bitmask-parser
  (insta/parser
    "alt = cat (<'|'> cat)*
     cat = term+
     <term> = <'('> alt <')'> | opt | plus | star | digit
     opt = term <'?'>
     plus = term <'+'>
     star = term <'*'>
     digit = '0' | '1'"
    :auto-whitespace :standard))

(def bitmask-transform
  {:alt (fn ([x] x) ([x & xs] (apply auto/or (cons x xs))))
   :cat (fn ([x] x) ([x & xs] (vec (cons x xs))))
   :opt auto/?
   :plus auto/+
   :star auto/*
   :digit (fn [x] (if (= x "0") 0 1))})

(defn- parse-bitmask-regex [regex-string]
  (auto/compile (insta/transform bitmask-transform (bitmask-parser regex-string))))

; Unfortunately, automat's advance function is too high-level for what we want to do
; Fortunately, automat lets us extract state and state transition info from the 
; metadata of the compiled automaton.

(defn- start-state [automaton]
  (-> automaton meta :fsm fsm/start))

(defn- accept-states [automaton]
  (-> automaton meta :fsm fsm/accept))

(defn maximum-sum [bitmask-regex-string s]
  (let [automaton (parse-bitmask-regex bitmask-regex-string)
        fsm (:fsm (meta automaton))
        start (start-state automaton),
        accepts (accept-states automaton), ; Note there can be more than one accepting state
        
        step-state-sum-map  ; the reducing function
        (fn [state-sum-map n]
          (apply merge-with max
                 (mapcat (fn [[state sum]] [{(fsm/next-state fsm state 0) sum}
                                            {(fsm/next-state fsm state 1) (+ sum n)}])
                         state-sum-map)))
        
        final (reduce step-state-sum-map {start 0} s) ]
    (apply max (map #(get final %) accepts))))

;=> (maximum-sum "0*1+0+1(0|1)*" [1 2 3 -4 5 -8 4])
;15
;=> (maximum-sum "0*1*0*" [1 2 3 -4 5 -8 4])
;7
             
; reduce-fsm isn't a very good fit for this problem, because it is focused more on
; using automata to perform reductions, and doesn't give us the option of
; low-level access to the state transitions.  But in case you're curious, here is
; how our non-segment-fsm looks in reduce-fsm

;(reduce-fsm/defsm non-segment-fsm
;  [[:start
;    0 -> :start
;    1 -> :found-run-of-1s]
;   [:found-run-of-1s
;    0 -> :found-run-of-0s
;    1 -> :found-run-of-1s]
;   [:found-run-of-0s
;    0 -> :found-run-of-0s
;    1 -> {:action (constantly true)} :found-second-run-of-1s]
;   [:found-second-run-of-1s
;    _ -> :found-second-run-of-1s]])
;
;Start the accumulator with false, and our action in the state machine will set it to true
;when we move to the final accepting state.
;
;=> (non-segment-fsm false [0 1 0 1])
;true
;=> (non-segment-fsm false [0 1 1 1])
;false

