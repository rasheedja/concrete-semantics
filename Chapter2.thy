theory Chapter2
  imports Main
begin

(* Exercise 2.1. Use the value command to evaluate the following expressions:
"1 + (2::nat )", "1 + (2::int )", "1 − (2::nat )" and "1 − (2::int )". *)

value "1 + (2::nat )"
value "1 + (2::int )"
value "1 - (2::nat )"
value "1 - (2::int )"

(* Exercise 2.2. Start from the definition of add given above. Prove that add
is associative and commutative. Define a recursive function double :: nat \<Rightarrow>
nat and prove double m = add m m. *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02 [simp]: "add m 0 = m"
  apply(induction m)
   apply(auto)
  done

lemma add_succ [simp]: "add n (Suc m) = Suc (add n m)"
  apply(induction n)
   apply(auto)
  done

lemma add_assoc [simp]: "add (add x y) z = add x (add y z)"
  apply(induction x)
   apply(auto)
  done

lemma add_comm [simp]: "add x y = add y x"
  apply(induction x)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc (Suc (double m))"

lemma double_equals_add_self [simp]: "double m = add m m"
  apply(induction m)
   apply(auto)
  done

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

(* Exercise 2.5. Define a recursive function sum_upto :: nat \<Rightarrow> nat such that
sum_upto n = 0 + ... + n and prove sum_upto n = n \<^emph> (n + 1) div 2. *)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) =(Suc n) + (sum_upto n)"

lemma sum_upto_equals [simp]: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

(* Exercise 2.6. Starting from the type 'a tree defined in the text, define a
function contents :: 'a tree \<Rightarrow> 'a list that collects all values in a tree in a list,
in any order, without removing duplicates. Then define a function sum_tree
:: nat tree \<Rightarrow> nat that sums up all values in a tree of natural numbers and
prove sum_tree t = sum_list (contents t ) (where sum_list is predefined). *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) =  a # contents(l) @ contents(r)" 

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + sum_tree(l) + sum_tree(r)"

lemma "sum_tree t = sum_list (contents t)"
  apply(induction t)
   apply(auto)
  done

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

(* Exercise 2.9. Write a tail-recursive variant of the add function on nat :
itadd. Tail-recursive means that in the recursive case, itadd needs to call
itself directly: itadd (Suc m) n = itadd . . .. Prove itadd m n = add m n. *)

lemma add_suc [simp]: "add m (Suc n) = Suc(add m n)"
  apply(induction m)
   apply(auto)
  done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0       m = m" |
"itadd (Suc m) n = itadd m (Suc n)"

value "itadd 3 2"

lemma "itadd m n = add m n"
  apply(induction m arbitrary: n)
   apply(auto)
  done

(* Exercise 2.10. Define a datatype tree0 of binary tree skeletons which do not
store any information, neither in the inner nodes nor in the leaves. Define a
function nodes :: tree0 \<Rightarrow> nat that counts the number of all nodes (inner
nodes and leaves) in such a tree. Consider the following recursive function:
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t )"
Find an equation expressing the size of a tree after exploding it (nodes
(explode n t )) as a function of nodes t and n. Prove your equation. You
may use the usual arithmetic operators, including the exponentiation opera-
tor “^”. For example, 2 ^ 2 = 4.
Hint: simplifying with the list of theorems algebra_simps takes care of
common algebraic properties of the arithmetic operators. *)

datatype tree0 = Leaf | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes (Leaf)     = 1" |
"nodes (Node l r) = Suc (nodes l + nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t       = t" |
"explode (Suc n) t = explode n (Node t t)"

(* Experimenting with explode and nodes *)

(* n is 1,2,3, and size of tree is 3 *)
value "nodes (Node (Leaf) (Leaf) :: tree0)"             (* 3 *)
value "nodes (explode 1 (Node (Leaf) (Leaf) :: tree0))" (* 7 *)
value "nodes (explode 2 (Node (Leaf) (Leaf) :: tree0))" (* 15 *)
value "nodes (explode 3 (Node (Leaf) (Leaf) :: tree0))" (* 31 *)

(* n is 1,2,3, and size of tree is 5 *)
value "nodes (Node (Node Leaf Leaf) (Leaf) :: tree0)"             (* 5 *)
value "nodes (explode 1 (Node (Node Leaf Leaf) (Leaf) :: tree0))" (* 11 *)
value "nodes (explode 2 (Node (Node Leaf Leaf) (Leaf) :: tree0))" (* 23 *)
value "nodes (explode 3 (Node (Node Leaf Leaf) (Leaf) :: tree0))" (* 47 *)

(* It seems that the formula is 2^n * (tree nodes count) + (2^n - 1) *)

theorem "let c = nodes t in (nodes (explode n t)) = (2^n * c) + (2^n - 1)"
  apply (simp add: Let_def)
  apply (induction n arbitrary: t)
   apply(auto simp add: algebra_simps)
  done

(* Exercise 2.11. Define arithmetic expressions in one variable over integers
(type int ) as a data type:
datatype exp = Var | Const int | Add exp exp | Mult exp exp
Define a function eval :: exp \<Rightarrow> int \<Rightarrow> int such that eval e x evaluates e at
the value x.
A polynomial can be represented as a list of coefficients, starting with the
constant. For example, [4, 2, − 1, 3] represents the polynomial 4+2x−x 2 +3x 3 .
Define a function evalp :: int list \<Rightarrow> int \<Rightarrow> int that evaluates a polynomial at
the given value. Define a function coeffs :: exp \<Rightarrow> int list that transforms an
expression into a polynomial. This may require auxiliary functions. Prove that
coeffs preserves the value of the expression: evalp (coeffs e) x = eval e x.
Hint: consider the hint in Exercise 2.10. *)

end
