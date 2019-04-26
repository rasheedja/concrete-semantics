theory Chapter5
  imports "~~/src/HOL/IMP/ASM"
begin

(* Exercise 5.1. Give a readable, structured proof of the following lemma: *)

lemma assumes T : "\<forall> x y. T x y \<or> T y x"
and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  from this and T have "T y x" by blast
  from this and TA have "A y x" by simp
  from this and `A x y` and A have "x = y" by simp
  from this and `T y x` have "T x y" by simp
  from this and `\<not> T x y` show "False" by simp
qed

(*
Exercise 5.2. Give a readable, structured proof of the following lemma:

lemma "\<exists> ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"

Hint: There are predefined functions take :: nat \<Rightarrow> 'a list \<Rightarrow> 'a list and drop
:: nat \<Rightarrow> 'a list \<Rightarrow> 'a list such that take k [x 1,. . .] = [x 1 ,. . .,x k ] and drop k
[x 1 ,. . .] = [x k +1 ,. . .]. Let sledgehammer find and apply the relevant take and
drop lemmas for you.
*)

lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
 (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)" (is "?P \<or> ?Q")
proof cases
  assume "even (length xs)" 
  then obtain k where lxs: "(length xs) = 2*k" by auto
  obtain ys where ys: "ys = take k xs" by simp
  obtain zs where zs: "zs = drop k xs" by simp
  from ys and lxs have lys: "length ys = k" by simp
  from zs and lxs have lzs: "length zs = k" by simp
  from ys and zs have "xs = ys @ zs" by simp
  moreover from lys and lzs have "length ys = length zs" by simp
  ultimately show ?thesis by blast
next
  assume "odd (length xs)"
  then obtain k where lxs: "(length xs) = 2*k + 1" using oddE by blast
  obtain ys where ys: "ys = take (Suc k) xs" by simp
  obtain zs where zs: "zs = drop (Suc k) xs" by simp
  from ys and lxs have lys: "length ys = (Suc k)" by simp
  from zs and lxs have lzs: "length zs = k" by simp
  from ys and zs have "xs = ys @ zs" by simp
  moreover from lys and lzs have "length ys = length zs + 1" by simp
  ultimately show ?thesis by blast
qed

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS : "ev n \<Longrightarrow> ev (Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

(* Simple exercise from 5.4.5 *)
lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))" then show False using ev.cases nat.distinct(1) by auto
qed

(* Exercise 5.4. Give a structured proof of \<not> ev (Suc (Suc (Suc 0))) by rule
inversions. If there are no cases to be proved you can close a proof immediately
with qed. *)
lemma "\<not> ev (Suc (Suc (Suc 0)))" (is "\<not> ?P")
proof
  assume "?P"
  hence "ev (Suc 0)" by cases
  thus False by cases
qed

(* Exercise 5.5. Recall predicate star from Section 4.5.2 and iter from Exer-
cise 4.4. Prove iter r n x y =\<Rightarrow> star r x y in a structured style; do not just
sledgehammer each case of the required induction. *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl : "star r x x" |
step : "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
it0 : "iter r 0 x x" |
itSS : "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "iter r n x y \<Longrightarrow> star r x y" (is "?P \<Longrightarrow> ?Q")
proof (induction rule: iter.induct)
  case (it0 x)
  then show ?case by (rule star.refl) 
next
  case (itSS x)
  then show ?case by (simp add: star.step)
qed

(* Exercise 5.6. Define a recursive function elems :: 'a list \<Rightarrow> 'a set and prove
x \<in> elems xs =\<Rightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<in>/ elems ys. *)

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x # xs) = {x} \<union> elems xs"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof cases
    assume "a = x"
    then show ?thesis by fastforce
  next
    assume "a \<noteq> x"
    moreover obtain ys zs where
    "ys = []" "zs = xs" by simp 
    ultimately show ?thesis by (metis Cons.prems Un_iff append.simps(2) elems.simps(2) empty_iff insert_iff local.Cons(1))
  qed
qed

(* Exercise 5.7. Extend Exercise 4.5 with a function that checks if some
alpha list is a balanced string of parentheses. More precisely, define a recursive
function balanced :: nat \<Rightarrow> alpha list \<Rightarrow> bool such that balanced n w is true
iff (informally) S (a n @ w ). Formally, prove that balanced n w = S (replicate
n a @ w ) where replicate :: nat \<Rightarrow> 'a \<Rightarrow> 'a list is predefined and replicate
n x yields the list [x , . . ., x ] of length n. *)

datatype alpha = ay | be | ce | de | ee | ef | ge 


inductive S :: "alpha list \<Rightarrow> bool" where
S0 : "S []" |
Sw : "S w \<Longrightarrow> S (a # w @ [b])" |
Sc : "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"


inductive T :: "alpha list \<Rightarrow> bool" where
T0 : "T []" |
Tw : "T w \<Longrightarrow> T x \<Longrightarrow> T (w @ [a] @ x @ [b])"

lemma T_comm: "T w \<Longrightarrow> T x \<Longrightarrow> T (x @ w)"
  apply(induction rule: T.induct)
   apply(simp)
  apply(metis Tw append_assoc)
  done

lemma T_implies_S: "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
   apply(metis S0)
  apply(simp add: Sw Sc)
  done

lemma S_implies_T: "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
    apply(metis T0)
   apply (metis Cons_eq_appendI T.simps self_append_conv2)
  apply(simp add: T_comm)
  done

theorem S_eq_T: "S w = T w"
  apply(auto simp add: T_implies_S S_implies_T)
  done

fun replicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"replicate 0 _ = []" |
"replicate n x = [x] @ (replicate (n - 1) x)"

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
(* not sure how to define this yet *)

lemma "balanced n w \<Longrightarrow> S (replicate n a @ w)"
