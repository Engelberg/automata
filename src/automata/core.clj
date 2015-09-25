(ns automata.core
  (:require reduce-fsm            
            [automat.core :as auto]
            [automat.fsm :as fsm]
            [automat.viz :refer [view save]]
            [clojure.math.combinatorics :as comb]
            [instaparse.core :as insta])
  (:refer-clojure :exclude [max max-key])
  (:use clojure.test))

;; ACKNOWLEDGEMENTS
; This is inspired by Chapter 11 of Pearls of Functional Algorithm Design by Richard Bird,
; a beautiful example of a programming puzzle that is elegantly solved with automata,
; and extraordinarily difficult to solve if you don't see the connection to automata.
; It extends the work in that book by showing how to use instaparse and automat to 
; generalize to other sum problems.

;; PRELUDE
; For the purposes of this code, it is useful to replace Clojure's max / max-key 
; with versions that return nil when passed no inputs to maximize.
(defn max ([] nil) ([& s] (apply clojure.core/max s)))
(defn max-key ([k] nil) ([k & s] (apply clojure.core/max-key k s)))

;; THE CLASSIC INTERVIEW PROBLEM - MAXIMUM SEGMENT SUM
; A popular problem is to find an O(n) algorithm for computing the maximum sum 
; achievable by adding up some contiguous subsequence (aka segment) of
; a sequence of numbers (typical input is a mix of positive and negative integers).

; For example,
;=> (maximum-segment-sum [-1 2 3 -4 5 -8 4])
;6
; because 2+3+-4+5 is 6

; If you've never seen this problem before, I encourage you to go try to solve
; it right now.  It's a fun problem.

; The trick is to keep a running sum as you traverse the sequence, 
; never letting the running sum dip below 0.  This has the effect of
; ignoring negative numbers that make things "too negative".
; Return the highest sum you saw.

; This strategy can be implemented concisely in Clojure:
(defn maximum-segment-sum [s] 
  (apply max (reductions (comp #(max 0 %) +) 0 s)))

; So, for example, when processing [-1 2 3 -4 5 -8 4], 
; (reductions step 0 s) is [0 0 2 5 1 6 0 4], and 6 is the max of that 

;; A HARDER PROBLEM - MAXIMUM NON-SEGMENT SUM

; But we're going to do something harder, we're looking for the maximum sum
; among subsequences that are *not* a continguous segment.

; For example,
; => (maximum-non-segment-sum [-1 4 5 -3 -4])
; 5
; because 4+5+-4 = 5, and those three numbers don't form a segment.
; We can't choose just 4, or just 5, or 4+5, because singletons and adjacent pairs
; are considered a segment.  We can't even choose the "empty" subsequence with a
; value of 0, because that is also considered a segment.
; We could have chosen things like -1+5 or 5+-4 or 4+-3, but they happen
; to be not as good.

; Unfortunately, there's no clever trick for solving this problem.
; We're going to have to look for a more principled approach.
; (If you don't believe me, go spend a while trying to solve it, just
; so you can appreciate how hard this problem really is.)

;; FIRST TRY - AN APPROACH THAT WORKS, BUT IS SLOW

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
; The automat library by Zach Tellman lets us easily build an automaton from a regex.

(def non-segment-automaton
  (auto/compile
    [(auto/* 0) (auto/+ 1) (auto/+ 0) 1 (auto/* (auto/or 0 1))]))

; Take a look at the automaton with (view non-segment-automaton)

; We use an automaton by making repeated calls to auto/advance.
; auto/advance takes an initial value (not relevant here) 
; or the outputted state from a previous call to auto/advance
; so it works well with Clojure's reduce.

; Here is an example of the successive states we get when we feed our automaton 0, 1, 0, 1

;=> (auto/advance non-segment-automaton nil 0)
;#automat.core.CompiledAutomatonState{:accepted? false, :checkpoint nil, :state-index 0, :start-index 0, :stream-index 1, :value nil}
;=> (auto/advance non-segment-automaton *1 1)
;#automat.core.CompiledAutomatonState{:accepted? false, :checkpoint nil, :state-index 1, :start-index 0, :stream-index 2, :value nil}
;=> (auto/advance non-segment-automaton *1 0)
;#automat.core.CompiledAutomatonState{:accepted? false, :checkpoint nil, :state-index 2, :start-index 0, :stream-index 3, :value nil}
;=> (auto/advance non-segment-automaton *1 1)
;#automat.core.CompiledAutomatonState{:accepted? true, :checkpoint nil, :state-index 3, :start-index 0, :stream-index 4, :value nil}

; Note that the :accepted? value of the state tells us whether we are in an "accepting state"
; So a bitmask represents a non-segment subsequence if we can feed it to this automaton
; and get to an accepting state

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
  (->> (apply comb/cartesian-product (repeat (count s) [0 1])) ; all bitmasks matching s's length
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

; This works! Try it out at the REPL on small-ish sequences
; => (maximum-non-segment-sum-slow-version [1 2 3 -4 5 -8 4])
; 15

; Here is an interesting case to consider:
;=> (maximum-non-segment-sum-slow-version [1 2])
;nil

; There is no non-segment subsequence if the sequence has fewer than 3 elements,
; so returning nil here is what we would expect.  You may recall, back in the prelude
; at the top of this file, I patched `max` so (max) would return nil.
; This is why I did that.  It keeps the code clean and elegant, properly returning nil
; when there are no subsequence sums to max, otherwise the function would throw an error

;; SECOND TRY - MAXIMUM NON-SEGMENT SUM IN ONE PASS

; The problem with the above version is that it is O(2^n)
; We can get this down to O(n) by cleverly interleaving the 
; automaton constraint checking with the summing/max process.
; As we do one pass through the sequence, our accumulator
; tracks the maximum sum we can get ending in a given state of our state machine.
; At the end of the pass, the value associated with the accepting state is our answer.
; See slides from the talk for a clear illustration of how this process works.

; Getting at the individual states and transitions of the automaton produced by automat
; is tricky, so for clarity, I've implemented this next function by simply
; encoding the states and transitions directly with Clojure maps 
; (where states are keywords, transitions are numbers 0 or 1)
; Next, I'll show how to do this more generally in automat.

(defn maximum-non-segment-sum [s]
  (let [transitions {:q0 {0 :q0, 1 :q1},
                     :q1 {0 :q2, 1 :q1},
                     :q2 {0 :q2, 1 :q3},
                     :q3 {0 :q3, 1 :q3}},
        
        step-state-sum-map     ; the reducing function
        (fn [state-sum-map n]
          (apply merge-with max
                 (mapcat (fn [[state sum]] [{((transitions state) 0) sum}
                                            {((transitions state) 1) (+ sum n)}])
                         state-sum-map)))]

  (get (reduce step-state-sum-map {:q0 0} s) :q3)))

; This works too, but is one pass, O(n), very fast.  Try it at the REPL.
;=> (maximum-non-segment-sum [1 2 3 -4 5 -8 4])
;15

;; GENERALIZING TO OTHER MAXIMUM SUM PROBLEMS

; The amazing thing is that the above O(n) strategy works for *any* maximum sum problem 
; where the subsequence constraint can be specified by a regular expression.
; So, for the grand finale, let's find the maximum-sum from an arbitrary bitmask regex

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
        
        final (reduce step-state-sum-map {start 0} s)]
    (apply max (keep #(get final %) accepts)))) 

; Now we can solve the maximum non-segment sum
;=> (maximum-sum "0*1+0+1(0|1)*" [1 2 3 -4 5 -8 4])
;15
; or just as easily, the maximum segment sum
;=> (maximum-sum "0*1*0*" [1 2 3 -4 5 -8 4])
;7
; or something crazy like the maximum sum of segments of length 3
; => (maximum-sum "0*111(0+111)*0*" [1 -1 2 4 -2 6 8])
; 14
 
;; SHOW ME THE MASK!

; Let's up the ante by tracking both the mask and the sum, so we can see where the sum came from
; The code is essentially the same as above, but instead of just tracking sums,
; we track a combination of the sum and the mask that got us there.

(def init-sum-mask {:sum 0, :mask []})
(defn- add-to-sum-mask [{:keys [sum mask]} n bit]
  {:sum (+ n sum) :mask (conj mask bit)}) 

(defn maximum-sum-mask [bitmask-regex-string s]
  (let [automaton (parse-bitmask-regex bitmask-regex-string)
        fsm (:fsm (meta automaton))
        start (start-state automaton),
        accepts (accept-states automaton), ; Note there can be more than one accepting state
        
        step-state-sum-map  ; the reducing function
        (fn [state-sum-map n]
          (apply merge-with (partial max-key :sum)
                 (mapcat (fn [[state sum-mask]] [{(fsm/next-state fsm state 0) 
                                                  (add-to-sum-mask sum-mask 0 0)}
                                                 {(fsm/next-state fsm state 1)
                                                  (add-to-sum-mask sum-mask n 1)}])
                         state-sum-map)))
        
        final (reduce step-state-sum-map {start init-sum-mask} s) ]
    (apply max-key :sum (keep #(get final %) accepts))))

;=> (maximum-sum-mask "0*1+0+1(0|1)*" [1 2 3 -4 5 -8 4])
;{:sum 15, :mask [1 1 1 0 1 0 1]}
;=> (maximum-sum-mask "0*1*0*" [1 2 3 -4 5 -8 4])
;{:sum 7, :mask [1 1 1 1 1 0 0]}
;=> (maximum-sum-mask "0*111(0+111)*0*" [1 -1 2 4 -2 6 8])
;{:sum 14, :mask [1 1 1 0 1 1 1]}

;; ANOTHER CLOJURE AUTOMATA LIBRARY - REDUCE-FSM

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

