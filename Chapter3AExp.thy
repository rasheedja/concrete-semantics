section "Arithmetic and Boolean Expressions"

(* Exercise 3.4. Take a copy of theory AExp and modify it as follows. Extend
type aexp with a binary constructor Times that represents multiplication.
Modify the definition of the functions aval and asimp accordingly. You can
remove asimp_const. Function asimp should eliminate 0 and 1 from multi-
plications as well as evaluate constant subterms. Update all proofs concerned. *)

theory Chapter3AExp imports Main begin

subsection "Arithmetic Expressions"

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

text_raw\<open>\snip{AExpaexpdef}{2}{1}{%\<close>
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp
text_raw\<open>}%endsnip\<close>

(* Extend aval to include Times *)

text_raw\<open>\snip{AExpavaldef}{1}{2}{%\<close>
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s" |
"aval (Times a1 a2) s = aval a1 s * aval a2 s"
text_raw\<open>}%endsnip\<close>

value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

text \<open>The same state more concisely:\<close>
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text \<open>A little syntax magic to write larger states compactly:\<close>

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

text \<open>\noindent
  We can now write a series of updates to the function @{text "\<lambda>x. 0"} compactly:
\<close>
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"


text \<open>In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
\<close>
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

text\<open>Note that this @{text"<\<dots>>"} syntax works for any function space
@{text"\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2"} where @{text "\<tau>\<^sub>2"} has a @{text 0}.\<close>


text\<open>Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors:\<close>

text_raw\<open>\snip{AExpplusdef}{0}{2}{%\<close>
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"
text_raw\<open>}%endsnip\<close>

lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
  done

(* Define times to eliminate 0s and 1s appropriately *)
fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"times (N n1) (N n2) = N (n1 * n2)" |
"times (N n) a = (if n=0 then (N 0) else (if n=1 then a else (Times (N n) a)))" |
"times a (N n) = (if n=0 then (N 0) else (if n=1 then a else (Times a (N n))))" |
"times a1 a2 = Times a1 a2"

lemma aval_times[simp]: "aval (times a1 a2) s = aval a1 s * aval a2 s"
  apply(induction a1 a2 rule: times.induct)
                      apply(simp_all)
  done

text_raw\<open>\snip{AExpasimpdef}{2}{0}{%\<close>
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
"asimp (Times a1 a2) = times (asimp a1) (asimp a2)"
text_raw\<open>}%endsnip\<close>

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

value "asimp (Times (Times (N 0) (N 0)) (Times (V ''x'') (N 0)))"
value "asimp (Times (Times (N 1) (N 1)) (Times (V ''x'') (N 0)))"
value "asimp (Times (Times (N 0) (N 0)) (Times (V ''x'') (N 1)))"
value "asimp (Times (Times (N 1) (N 1)) (Times (V ''x'') (N 1)))"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induction a)
apply simp_all
done

end
