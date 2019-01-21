theory MyAdd
  imports Main
begin

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

(* Exercise 2.5. Define a recursive function sum_upto :: nat \<Rightarrow> nat such that
sum_upto n = 0 + ... + n and prove sum_upto n = n \<^emph> (n + 1) div 2. *)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) =(Suc n) + (sum_upto n)"

lemma sum_upto_equals [simp]: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

end
