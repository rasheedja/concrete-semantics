theory CountLtLength
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
