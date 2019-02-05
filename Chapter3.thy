theory Chapter3
  imports Main
          "~~/src/HOL/IMP/AExp"          
begin

(* Exercise 3.1. To show that asimp_const really folds all subexpressions of
the form Plus (N i ) (N j ), define a function optimal :: aexp \<Rightarrow> bool that
checks that its argument does not contain a subexpression of the form Plus
(N i ) (N j ). Then prove optimal (asimp_const a). *)

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus a1 a2) = (optimal a1 & optimal a2)"

lemma "optimal (asimp_const a)"
  apply(induction a)
   apply(auto split: aexp.split)
  done

(* Exercise 3.2. In this exercise we verify constant folding for aexp where we
sum up all constants, even if they are not next to each other. For example, Plus
(N 1) (Plus (V x ) (N 2)) becomes Plus (V x ) (N 3). This goes beyond asimp.
Define a function full_asimp :: aexp \<Rightarrow> aexp that sums up all constants and
prove its correctness: aval (full_asimp a) s = aval a s. *)

(* Strategy: Add all the constants first, ignoring variables. Then, add variables
to result using asimp *)

(* Add all constants, zero out variables *)
fun addN :: "aexp \<Rightarrow> int" where
"addN (N n) = n" |
"addN (V x) = 0" |
"addN (Plus a1 a2) = addN a1 + addN a2"

(* Manually checking that addN works as expected *)
value "addN (Plus (N 1) (Plus (V x) (N 2)))"
value "addN (Plus (N 1) (Plus (N 2) (V x)))"
value "addN (Plus (N 1) (Plus (N 2) (N 2)))"
value "addN (Plus (V x) (Plus (N 2) (N 2)))"

(* Add all variables, zero out constants *)
fun addV :: "aexp \<Rightarrow> aexp" where
"addV (N n) = N 0" |
"addV (V x) = V x" |
"addV (Plus a1 a2) = Plus (addV a1) (addV a2)"


(* Manually checking that addN works as expected *)
value "addV (Plus (N 1) (Plus (N 2) (N 2)))"
value "addV (Plus (V x) (Plus (N 2) (N 2)))"
value "addV (Plus (N 1) (Plus (V x) (N 2)))"
value "addV (Plus (N 1) (Plus (N 2) (V x)))"
value "addV (Plus (V x) (Plus (V y) (N 2)))"
value "addV (Plus (V x) (Plus (N 2) (V y)))"
value "addV (Plus (N 1) (Plus (V x) (V y)))"
value "addV (Plus (V x) (Plus (V y) (V z)))"

(* Define a function that combines the results of addN and addV *)
definition addNV :: "aexp \<Rightarrow> aexp" where
"addNV a = Plus (N (addN a)) (addV a)"

lemma addNV_equals_simp [simp]: "aval (addNV a) s = aval a s"
  apply(simp add: addNV_def)
  apply(induction a)
    apply(auto)
  done

(* fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n) = N n" |
"full_asimp (V x) = V x" |
"full_asimp (Plus a1 (Plus a2 a3)) = plus (full_asimp a1) (plus (full_asimp a2) (full_asimp a3))" |
"full_asimp (Plus (Plus a1 a2) a3) = plus (plus (full_asimp a1) (full_asimp a2)) (full_asimp a3)" |
"full_asimp (Plus a1 a2) = plus (full_asimp a1) (full_asimp a2)"
*)

(* Use addNV to define full_asimp, simplifying the aexp before passing it to asimp *)
definition full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = asimp (addNV a)"

(* Manually verify that full_asimp works as expected *)
value "full_asimp (Plus (N 1) (Plus (V x) (V y)))"
value "full_asimp (Plus (N 1) (Plus (V x) (N 2)))"
value "full_asimp (Plus (N 1) (Plus (N 2) (V x)))"
value "full_asimp (Plus (N 1) (Plus (N 2) (N 3)))"
value "full_asimp (Plus (V x) (Plus (N 2) (N 3)))"
value "full_asimp (Plus (V x) (Plus (V y) (N 3)))"
value "full_asimp (Plus (V x) (Plus (N 2) (V y)))"
value "full_asimp (Plus (V x) (Plus (V y) (V z)))"

lemma "aval (full_asimp a) s = aval a s"
  apply(simp add: full_asimp_def)
  done

(* Exercise 3.3. Substitution is the process of replacing a variable by an ex-
pression in an expression. Define a substitution function subst :: vname \<Rightarrow>
aexp \<Rightarrow> aexp \<Rightarrow> aexp such that subst x a e is the result of replacing every
occurrence of variable x by a in e. For example:

subst ''x'' (N 3) (Plus (V ''x'' ) (V ''y'' )) = Plus (N 3) (V ''y'' )

Prove the so-called substitution lemma that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
aval (subst x a e) s = aval e (s(x := aval a s)). As a consequence prove
aval a 1 s = aval a 2 s =\<Rightarrow> aval (subst x a 1 e) s = aval (subst x a 2 e) s. *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V y) = (if x = y then a else (V y))" |
"subst x a (Plus a1 a2) = Plus (subst x a a1) (subst x a a2)"

lemma subst_lemma: "aval (subst x a e) s = aval e (s (x := aval a s))"
  apply(induction e)
    apply(auto)
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(simp add: subst_lemma)
  done

(* Exercise 3.4. Take a copy of theory AExp and modify it as follows. Extend
type aexp with a binary constructor Times that represents multiplication.
Modify the definition of the functions aval and asimp accordingly. You can
remove asimp_const. Function asimp should eliminate 0 and 1 from multi-
plications as well as evaluate constant subterms. Update all proofs concerned. *)

(* See Chapter3AExp.thy *)

end