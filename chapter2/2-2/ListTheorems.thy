theory ListTheorems
  imports Main
begin

(* Exercise 2.3. Define a function count :: 0 a \<Rightarrow> 0 a list \<Rightarrow> nat that counts the
number of occurrences of an element in a list. Prove count x xs 6 length xs. *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x xs = (if x = hd(xs) then Suc (count x (tl xs)) else count x (tl xs))"

lemma count_lt_length [simp]: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(* Exercise 2.4. Define a recursive function snoc :: 0 a list \<Rightarrow> 0 a \<Rightarrow> 0 a list
that appends an element to the end of a list. With the help of snoc define
a recursive function reverse :: 0 a list \<Rightarrow> 0 a list that reverses a list. Prove
reverse (reverse xs) = xs. *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (x # xs) y = x # (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]: "reverse (snoc xs x) = x # (reverse xs)"
  apply(induction xs)
   apply(auto)
  done

lemma reverse_reverse_identity [simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done
