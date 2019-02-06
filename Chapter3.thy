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

(* Exercise 3.5. Define a datatype aexp2 of extended arithmetic expressions
that has, in addition to the constructors of aexp, a constructor for modelling
a C-like post-increment operation x++, where x must be a variable. Define an
evaluation function aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state that returns both
the value of the expression and the new state. The latter is required because
post-increment changes the state.
Extend aexp2 and aval2 with a division operation. Model partiality of
division by changing the return type of aval2 to (val \<times> state) option. In
case of division by 0 let aval2 return None. Division on int is the infix div. *)

datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | Increment2 vname | Divide2 aexp2 aexp2

(* Used this to learn how to work with the option syntax: 
https://github.com/gsomix/concrete-semantics-solutions/blob/cf1b864744f80091a1f91a85b14b3d8edf7e0f9f/Chapter3.thy#L144 *)

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (N2 n) s = Some (n, s)" |
"aval2 (V2 v) s = Some (s v, s)" |
"aval2 (Plus2 a1 a2) s = Option.bind (aval2 a1 s) (\<lambda> (a1val, s1).
                        Option.bind (aval2 a2 s1) (\<lambda> (a2val, s2).
                        Some (a1val + a2val, s2)))" |
"aval2 (Increment2 x) s = Some ((s x), s (x := (s x) + 1))" |
"aval2 (Divide2 a1 a2) s = Option.bind (aval2 a1 s) (\<lambda> (a1val, s1).
                          Option.bind (aval2 a2 s1) (\<lambda> (a2val, s2).
                          if a2val = 0 then None else Some ((a1val div a2val), s2)))"

(* Manually checking that everything works as expected *)
value "aval2 (Plus2 (Increment2 ''x'') (Divide2 (N2 10) (V2 ''x''))) (<''x'' := -1>)"
value "aval2 (Plus2 (Increment2 ''x'') (Divide2 (N2 10) (V2 ''x''))) (<''x'' := 0>)"
value "aval2 (Plus2 (Increment2 ''x'') (Divide2 (N2 10) (V2 ''x''))) (<''x'' := 1>)"
value "aval2 (Plus2 (Increment2 ''x'') (Divide2 (N2 10) (V2 ''x''))) (<''x'' := 2>)"
value "aval2 (Plus2 (Increment2 ''x'') (Divide2 (N2 10) (V2 ''x''))) (<''x'' := 3>)"
value "aval2 (Plus2 (Increment2 ''x'') (Divide2 (N2 10) (V2 ''x''))) (<''x'' := 4>)"

(* Exercise 3.6. The following type adds a LET construct to arithmetic ex-
pressions:

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

The LET constructor introduces a local variable: the value of LET x e 1 e 2
is the value of e 2 in the state where x is bound to the value of e 1 in the
original state. Define a function lval :: lexp \<Rightarrow> state \<Rightarrow> int that evaluates
lexp expressions. Remember s(x := i ).
Define a conversion inline :: lexp \<Rightarrow> aexp. The expression LET x e 1 e 2
is inlined by substituting the converted form of e 1 for x in the converted form
of e 2. See Exercise 3.3 for more on substitution. Prove that inline is correct
w.r.t. evaluation. *)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl n) s = n" |
"lval (Vl v) s = s v" |
"lval (Plusl a1 a2) s = (lval a1 s) + (lval a2 s)" |
"lval (LET x e1 e2) s = lval e2 (s(x := (lval e1 s)))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = N n" |
"inline (Vl v) = V v" |
"inline (Plusl a1 a2) = Plus (inline a1) (inline a2)" |
"inline (LET x e1 e2) = subst x (inline e1) (inline e2)"

lemma inline_lexp_equals_aexp: "lval e s = aval (inline e) s"
  apply(induction e arbitrary: s)
     apply(simp_all add: subst_lemma)
  done

end