theory IntersperseMapComm
  imports Main
begin

(* Exercise 2.8. Define a function intersperse :: 'a \<Rightarrow> 'a list \<Rightarrow> 'a list such
that intersperse a [x 1 , ..., x n ] = [x 1 , a, x 2 , a, ..., a, x n ]. Now prove that
map f (intersperse a xs) = intersperse (f a) (map f xs). *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (x # xs) = [x, a] @ (intersperse a xs)"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
   apply(auto)
  done

end
