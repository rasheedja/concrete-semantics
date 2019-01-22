theory BinaryTreePrePostReverse
  imports Main
begin

(* Exercise 2.7. Define a new type 'a tree2 of binary trees where values are
also stored in the leaves of the tree. Also reformulate the mirror function
accordingly. Define two functions pre_order and post_order of type 'a tree2
\<Rightarrow> 'a list that traverse a tree and collect all stored values in the respective
order in a list. Prove pre_order (mirror t ) = rev (post_order t ). *)

datatype 'a tree2 = Leaf 'a | Node 'a "'a tree2" "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Leaf a) = Leaf a" |
"mirror (Node a l r) = Node a (mirror r) (mirror l)"

(* pre_order traversal: root, left, right *)
fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf a) = [a]" |
"pre_order (Node a l r) = [a] @ (pre_order l) @ (pre_order r)"

(* post_order traversal: left, right, root *)
fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Node a l r) = (post_order l) @ (post_order r) @ [a]" |
"post_order (Leaf a) = [a]"

lemma pre_order_mirror_equal_rev_post_order [simp]: "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
   apply(auto)
  done

end
