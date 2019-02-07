theory Chapter3
  imports "~~/src/HOL/IMP/BExp"
          "~~/src/HOL/IMP/ASM"          
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

(* Exercise 3.7. Define functions Eq, Le :: aexp \<Rightarrow> aexp \<Rightarrow> bexp and prove
bval (Eq a 1 a 2 ) s = (aval a 1 s = aval a 2 s) and bval (Le a 1 a 2) s =
(aval a 1 s \<le> aval a 2 s). *)

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b1 b2 = Not (And (Not b1) (Not b2))"

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq b1 b2 = And (Not (Less b1 b2)) (Not (Less b2 b1))"

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le b1 b2 = Or (Eq b1 b2) (Less b1 b2)"

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply(auto simp add: Eq_def)
  done

lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply(auto simp add: Le_def Or_def Eq_def)
  done

(* Exercise 3.8. Consider an alternative type of boolean expressions featuring
a conditional:

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

First define an evaluation function ifval :: ifexp \<Rightarrow> state \<Rightarrow> bool analogously
to bval. Then define two functions b2ifexp :: bexp \<Rightarrow> ifexp and if2bexp ::
ifexp \<Rightarrow> bexp and prove their correctness, i.e., that they preserve the value
of an expression. *)

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 v) s = v" |
"ifval (If i1 i2 i3) s = (if (ifval i1 s) then (ifval i2 s) else (ifval i3 s))" |
"ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v) = (Bc2 v)" |
"b2ifexp (Not b) = (If (b2ifexp b) (Bc2 False) (Bc2 True))" |
"b2ifexp (And b1 b2) = (If (b2ifexp b1) (
                        (If (b2ifexp b2) (Bc2 True) (Bc2 False))
                       ) (Bc2 False))" |
"b2ifexp (Less a1 a2) = Less2 a1 a2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v) = (Bc v)" |
"if2bexp (If i1 i2 i3) = Or (And (if2bexp i1) (if2bexp i2)) (And (Not (if2bexp i1)) (if2bexp i3))" |
"if2bexp (Less2 a1 a2) = Less a1 a2"

lemma ifval_b2ifexp: "ifval (b2ifexp b) s = bval b s"
  apply(induction b)
     apply(simp_all)
  done

lemma bval_if2bexp: "bval (if2bexp i) s = ifval i s"
  apply(induction i)
    apply(simp_all add: Or_def)
  done

(* Exercise 3.9. Define a new type of purely boolean expressions

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

where variables range over values of type bool:

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x ) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b 1 b 2 ) s = (pbval b1 s \<and> pbval b 2 s)" |
"pbval (OR b 1 b 2 ) s = (pbval b1 s \<or> pbval b 2 s)"

Define a function is_nnf :: pbexp \<Rightarrow> bool that checks whether a boolean
expression is in NNF (negation normal form), i.e., if NOT is only applied
directly to VARs. Also define a function nnf :: pbexp \<Rightarrow> pbexp that converts
a pbexp into NNF by pushing NOT inwards as much as possible. Prove that
nnf preserves the value (pbval (nnf b) s = pbval b s) and returns an NNF
(is_nnf (nnf b)).
An expression is in DNF (disjunctive normal form) if it is in NNF and if
no OR occurs below an AND. Define a corresponding test is_dnf :: pbexp \<Rightarrow>
bool. An NNF can be converted into a DNF in a bottom-up manner. The crit-
ical case is the conversion of AND b 1 b 2 . Having converted b 1 and b 2 , apply
distributivity of AND over OR. Define a conversion function dnf_of_nnf ::
pbexp \<Rightarrow> pbexp from NNF to DNF. Prove that your function preserves the
value (pbval (dnf_of_nnf b) s = pbval b s) and converts an NNF into a
DNF (is_nnf b =\<Rightarrow> is_dnf (dnf_of_nnf b)). *)

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2 ) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2 ) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR x)) = True" |
"is_nnf (NOT b) = False" |
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (OR b1 b2) = (is_nnf b1 \<or> is_nnf b2)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = (VAR x)" |
"nnf (NOT (VAR x)) = (NOT (VAR x))" |
"nnf (NOT (OR b1 b2)) = AND (nnf (NOT b1)) (nnf (NOT b2))" |
"nnf (NOT (AND b1 b2)) = OR (nnf (NOT b1)) (nnf (NOT b2))" |
"nnf (NOT (NOT b)) = nnf b" |
"nnf (AND b1 b2) = AND (nnf b1) (nnf b2)" |
"nnf (OR b1 b2) = OR (nnf b1) (nnf b2)"

lemma ppbval_nnf [simp]: "pbval (nnf b) s = pbval b s"
  apply(induction b arbitrary: s rule: nnf.induct)
        apply(simp_all)
  done

lemma is_nnf_nnf: "is_nnf (nnf b)"
  apply(induction b rule: nnf.induct)
        apply(simp_all)
  done

fun is_dnf :: "pbexp \<Rightarrow> bool"  where
"is_dnf (AND (OR _ _) _) = False" |
"is_dnf (AND _ (OR _ _)) = False" |
"is_dnf (AND b1 b2) = (is_dnf b1 \<and> is_dnf b2)" |
"is_dnf (OR b1 b2) = (is_dnf b1 \<or> is_dnf b2)" |
"is_dnf b = is_nnf b"

(* Apply distributivity of AND over OR *)
fun dnf_dist :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"dnf_dist c (OR b1 b2) = OR (dnf_dist c b1) (dnf_dist c b2)" |
"dnf_dist (OR b1 b2) c = OR (dnf_dist b1 c) (dnf_dist b2 c)" |
"dnf_dist b1 b2 = AND b1 b2"

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = (VAR x)" |
"dnf_of_nnf (NOT x) = (NOT x)" |
"dnf_of_nnf (AND b1 b2) = dnf_dist (dnf_of_nnf b1) (dnf_of_nnf b2)" |
"dnf_of_nnf (OR b1 b2) = OR (dnf_of_nnf b1) (dnf_of_nnf b2)"

lemma pbval_dnf_dist: "pbval (dnf_dist b1 b2) s = pbval (AND b1 b2) s"
  apply(induction b1 b2 rule: dnf_dist.induct)
              apply(auto)
  done

lemma is_dnf_dnf_dist: "is_dnf b1 \<and> is_dnf b2 \<Longrightarrow> is_dnf (dnf_dist b1 b2)"
  apply(induction b1 b2 rule: dnf_dist.induct)
              apply(auto)
  done

lemma pbval_dnf_of_nnf [simp]:  "(pbval (dnf_of_nnf b) s = pbval b s)"
  apply(induction b rule:dnf_of_nnf.induct)
     apply(simp_all add: pbval_dnf_dist)
  done

lemma is_dnf_dnf_of_nnf: "(is_nnf b ==> is_dnf (dnf_of_nnf b))"
  apply(induction b rule:dnf_of_nnf.induct)
     apply(auto simp add: is_dnf_dnf_dist)
  done

(* Exercise 3.11. This exercise is about a register machine and compiler for
aexp. The machine instructions are

datatype instr = LDI int reg | LD vname reg | ADD reg reg

where type reg is a synonym for nat. Instruction LDI i r loads i into register
r, LD x r loads the value of x into register r, and ADD r 1 r 2 adds register
r 2 to register r 1 .
Define the execution of an instruction given a state and a register state
(= function from registers to integers); the result is the new register state:

fun exec1 :: instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int ) \<Rightarrow> reg \<Rightarrow> int

Define the execution exec of a list of instructions as for the stack machine.
The compiler takes an arithmetic expression a and a register r and pro-
duces a list of instructions whose execution places the value of a into r. The
registers > r should be used in a stack-like fashion for intermediate results,
the ones < r should be left alone. Define the compiler and prove it correct:
t. *)

type_synonym reg = nat

datatype instr = LDI int reg | LD vname reg | ADD reg reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec1 (LDI i r) _ rs = rs(r := i)" |
"exec1 (LD v r) s rs = rs(r := s v)" |
"exec1 (ADD r1 r2) _ rs = rs(r1 := rs r1 + rs r2)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec [] _ rs = rs" |
"exec (i#is) s rs = exec is s (exec1 i s rs)"

lemma reg_exec_append: "exec (is1@is2) s rs = exec is2 s (exec is1 s rs)"
  apply(induction is1 arbitrary: rs)
  apply(simp_all)
done

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
"comp (N n) r = [LDI n r]" |
"comp (V v) r = [LD v r]" |
"comp (Plus a1 a2) r = comp a1 r @ comp a2 (r+1) @ [ADD r (r+1)]"

lemma reg_exec_order: "r2 > r1 \<Longrightarrow> exec (comp a r2) s rs r1 = rs r1"
  apply(induction a arbitrary: r1 r2 rs)
    apply(auto simp add: reg_exec_append)
  done

theorem "exec (comp a r) s rs r = aval a s"
  apply(induction a arbitrary: r rs)
    apply(auto simp add: reg_exec_append reg_exec_order)
  done

(* Exercise 3.12. This is a variation on the previous exercise. Let the instruc-
tion set be

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

All instructions refer implicitly to register 0 as the source (MV0) or target
(all others). Define a compiler pretty much as explained above except that
the compiled code leaves the value of the expression in register 0. Prove that
exec (comp a r ) s rs 0 = aval a s. *)

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec01 (LDI0 i) _ rs = rs(0 := i)" |
"exec01 (LD0 v) s rs = rs(0 := s v)" |
"exec01 (MV0 r) s rs = rs(r := rs 0)" |
"exec01 (ADD0 r) _ rs = rs(0 := rs 0 + rs r)"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec0 [] _ rs = rs" |
"exec0 (i#is) s rs = exec0 is s (exec01 i s rs)"

lemma reg0_exec_append: "exec0 (is1@is2) s rs = exec0 is2 s (exec0 is1 s rs)"
  apply(induction is1 arbitrary: rs)
  apply(simp_all)
done

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (N n) _ = [LDI0 n]" |
"comp0 (V v) _ = [LD0 v]" |
"comp0 (Plus a1 a2) r = comp0 a1 r @ [MV0 (r+1)] @ comp0 a2 (r+1) @ [ADD0 (r+1)]"

lemma reg0_exec_order: "(r1 \<noteq> 0 \<and> r2 \<ge> r1) \<Longrightarrow> exec0 (comp0 a r2) s rs r1 = rs r1"
  apply(induction a arbitrary: r1 r2 rs)
    apply(auto simp add: reg0_exec_append)
  done

theorem "exec0 (comp0 a r) s rs 0 = aval a s"
  apply(induction a arbitrary: r rs)
    apply(auto simp add: reg0_exec_append reg0_exec_order)
  done

end
