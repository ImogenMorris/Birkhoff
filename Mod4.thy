theory Mod4 imports Main Real begin

definition eq4 :: "real \<Rightarrow> real \<Rightarrow> bool" (infix "=4" 61)
where "((a::real) =4 b) = (\<exists>(n::int). a = b+(4::int)*n)"

lemma eq4_bestdef: "a =4 b \<Longrightarrow> a =4 b+(4::int)*n"
proof -
  assume "a =4 b"
  then have "(\<exists>(m::int). a = b+(4::int)*m)" by (subst eq4_def[symmetric])
  then obtain m where "a = b+(4::int)*m" by (rule exE)
  also have "... = b+(4::int)*m - (4::int)*n + (4::int)*n" by simp
  also have "... = b + (4::int)*n + (4::int)*(m-n)" by simp
  finally show "a =4 b+(4::int)*n" using eq4_def by blast
qed
  
lemma eq4_refl: "a =4 a" using eq4_def by auto

lemma eq4_sym: "a =4 b \<Longrightarrow> b =4 a"
proof -
  assume "a =4 b"
  then have "(\<exists>(n::int). a = b+(4::int)*n)" by (subst eq4_def[symmetric])
  then obtain n where "a = b+(4::int)*n" by (rule exE)
  then have "b = a+4*((-n)::int)" by simp
  then have "(\<exists>(n::int). b = a+(4::int)*n)" by (rule exI)
  then show "b =4 a" by (subst eq4_def)
qed


lemma eq4_trans [trans]: "\<lbrakk>a =4 b; b =4 c\<rbrakk> \<Longrightarrow> a =4 c"
proof -
  assume "a =4 b"
  then have "(\<exists>(n::int). a = b+(4::int)*n)" by (subst eq4_def[symmetric])
  then obtain n where n_def:"a = b+(4::int)*n" by (rule exE)
  assume "b =4 c"
  then have "(\<exists>(m::int). b = c+(4::int)*m)" by (subst eq4_def[symmetric])
  then obtain m where m_def:"b = c+(4::int)*m" by (rule exE)
  from n_def have "a =  c+(4::int)*m +(4::int)*n" by (subst(asm) m_def)
  also have "... = c+(4::int)*(m+n)" by simp
  finally show "a =4 c" using eq4_def by blast
qed

definition mod4 :: "real \<Rightarrow> real" 
where "(mod4 (a::real)) = (THE b. 0\<le>b \<and> b < 4 \<and> a =4 b)"

lemma nat_consec4div:"(\<exists>(n::nat). l = 4*n) \<or> (\<exists>n. l+1 = 4*n) \<or> (\<exists>n. l+2 = 4*n) \<or> (\<exists>n. l+3 = 4*n)"
proof (induct l)
  case 0
  have "0 = 4 * (0::nat)" by simp
  then show ?case by fast
next
  case IH:(Suc l)
  then consider "\<exists>n. l = 4 * n"|"\<exists>n. l + 1 = 4 * n"|"\<exists>n. l + 2 = 4 * n"|"\<exists>n. l + 3 = 4 * n"
    by blast
  then show ?case
  proof (cases)
    assume "\<exists>n. l = 4 * n" then have "\<exists>n. l+4 = 4 * n" by presburger
    then show ?case by presburger
  next
    assume "\<exists>n. l + 1 = 4 * n" then show ?case by presburger
  next
    assume "\<exists>n. l + 2 = 4 * n" then show ?case by presburger
  next
    assume "\<exists>n. l + 3 = 4 * n" then show ?case by presburger 
  qed
qed 

lemma neg_nat:"(-(n::nat) = -(m::nat)) = ((n::nat) = (m::nat))" by simp

lemma negnat_consec4div:"(\<exists>(n::int). -(l::nat) = 4*n) \<or> (\<exists>n. -l-1 = 4*n) \<or> (\<exists>n. -l-2 = 4*n) \<or> (\<exists>n. -l-3 = 4*n)"
proof -
  from nat_consec4div
  have "(\<exists>(n::nat). -(l::nat) = -((4*n)::nat)) \<or> (\<exists>n. -((l+1)::nat) = -((4*n)::nat))
               \<or> (\<exists>n. -((l+2)::nat) = -((4*n)::nat)) \<or> (\<exists>n. -((l+3)::nat) = -((4*n)::nat))"
    by (subst neg_nat, subst neg_nat, subst neg_nat, subst neg_nat)
  have "(\<exists>(n::nat). -(l::nat) = 4*(-(n::nat))) \<or> (\<exists>n. -((l+1)::nat) = 4*(-(n::nat)))
               \<or> (\<exists>n. -((l+2)::nat) = 4*(-(n::nat))) \<or> (\<exists>n. -((l+3)::nat) = 4*(-(n::nat)))"
    by presburger
  then have "(\<exists>(n::int). -(l::nat) = 4*n) \<or> (\<exists>(n::int). -((l+1)::nat) = 4*n)
               \<or> (\<exists>(n::int). -((l+2)::nat) = 4*n) \<or> (\<exists>(n::int). -((l+3)::nat) = 4*n)" 
    by presburger
  then show ?thesis by presburger
qed


lemma int_consec4div:"(\<exists>(n::int). (k::int) = 4 * n) \<or> (\<exists>n. (k::int) + 1 = 4*n)
                           \<or> (\<exists>n. (k::int)+2 = 4*n) \<or> (\<exists>n. (k::int)+3 = 4*n)"
proof (cases "k\<ge>0")
  assume "k\<ge>0"
  then show ?thesis using nat_consec4div by presburger
next
  assume "\<not>k\<ge>0"
  then have "\<exists>(n::nat). k = -n" by presburger
  then show ?thesis using negnat_consec4div by presburger
qed

lemma noteq_int_diff:  assumes "(m::int) \<noteq> (n::int)"
      shows "(m-n \<ge> 1) \<or> (n-m \<ge> 1)" 
proof -
  from assms have "m-n \<noteq> 0" by simp
  then show ?thesis by force
qed

lemma eq4_ex_unique: "\<exists>!b. 0 \<le> b \<and> b < 4 \<and> a =4 b"
proof -
    have a_bds:"\<lfloor>a\<rfloor>\<le>a \<and> a<\<lfloor>a\<rfloor>+1" by linarith
    consider "(\<exists>n. \<lfloor>a\<rfloor> = 4 * n)"| "(\<exists>n. \<lfloor>a\<rfloor> + 1 = 4 * n) "
         |"(\<exists>n. \<lfloor>a\<rfloor> + 2 = 4 * n) "|" (\<exists>n. \<lfloor>a\<rfloor> + 3 = 4 * n)" using int_consec4div by blast
    then have "\<exists>(n::int). 4*n\<le>(a::real) \<and> a<4*(n::int)+4"
    proof (cases)
      assume "\<exists>n. \<lfloor>a\<rfloor> = 4 * n"
      from this a_bds show ?thesis by fastforce
    next
      assume "\<exists>n. \<lfloor>a\<rfloor>+1 = 4 * n"
      then obtain n where "\<lfloor>a\<rfloor>+1 = 4 * n" by (rule exE)
      then have "\<lfloor>a\<rfloor> = 4 * n -1" by algebra
      from this a_bds have "4*(n-1)\<le> a \<and> a<4*(n-1) +4" by auto
      then show ?thesis by blast
    next
      assume "\<exists>n. \<lfloor>a\<rfloor>+2 = 4 * n"
      then obtain n where "\<lfloor>a\<rfloor>+2 = 4 * n" by (rule exE)
      then have "\<lfloor>a\<rfloor> = 4 * n -2" by algebra
      from this a_bds have "4*(n-1)\<le> a \<and> a<4*(n-1) +4" by auto
      then show ?thesis by blast
    next
      assume "\<exists>n. \<lfloor>a\<rfloor>+3 = 4 * n"
      then obtain n where "\<lfloor>a\<rfloor>+3 = 4 * n" by (rule exE)
      then have "\<lfloor>a\<rfloor> = 4 * n -3" by algebra
      from this a_bds have "4*(n-1)\<le> a \<and> a<4*(n-1) +4" by auto
      then show ?thesis by blast
    qed
    then obtain n where "4*n\<le>(a::real) \<and> a<4*(n::int)+4" by force
    then have "0\<le>(a-4*n) \<and> (a-4*n) < 4 \<and> (a = (a-4*n)+(4::int)*n)" by force
    then have "0\<le>(a-4*n) \<and> (a-4*n) < 4 \<and> (\<exists>(m::int). a = (a-4*n)+(4::int)*m)" by blast
    then have "\<exists> (b::real). 0\<le>b \<and> b < 4 \<and> (\<exists>(m::int). a = b+(4::int)*m)" by blast
    then have "\<exists>b. 0\<le>b \<and> b < 4 \<and> a =4 b" using eq4_def by presburger
    have "\<forall> b c. 0\<le>b \<and> b < 4 \<and> a =4 b \<longrightarrow> 0\<le>c \<and> c < 4 \<and> a =4 c \<longrightarrow> b=c"
    proof (rule allI, rule allI, rule impI, rule impI, rule ccontr)
      fix b c
      assume "0\<le>b \<and> b < 4 \<and> a =4 b"
      assume "0\<le>c \<and> c < 4 \<and> a =4 c"
      assume "b \<noteq> c"
      from `0\<le>c \<and> c < 4 \<and> a =4 c` eq4_def obtain m where m_def:"a = c+4*(m::int)"
        by auto
      from `0\<le>b \<and> b < 4 \<and> a =4 b` eq4_def obtain n where n_def:"a = b+4*(n::int)" 
        by auto
      from m_def n_def have "b = c + 4*(m-n)" by force
      from m_def n_def `b \<noteq> c` have "(m::int) \<noteq> (n::int)" by force
      then have "m-n \<noteq> 0" by simp
      then have "(m-n \<ge> 1) \<or> (n-m \<ge> 1)" by fastforce
      from `b = c + 4*(m-n)` this `0\<le>b \<and> b < 4 \<and> a =4 b` have "\<not> (0\<le>c \<and> c < 4)" 
        by force
      from this `0\<le>c \<and> c < 4 \<and> a =4 c` show False by blast
    qed
    from this `\<exists>b. 0\<le>b \<and> b < 4 \<and> a =4 b` show ?thesis by blast
  qed


lemma mod4_bestdef: "0\<le> mod4 a" "mod4 a < 4" "a =4 mod4 a"
proof -
  from eq4_ex_unique have "0 \<le> mod4 a \<and> mod4 a < 4 \<and> a =4 mod4 a" 
    by (subst mod4_def, subst mod4_def, subst mod4_def, rule theI')
  then show "0 \<le> mod4 a" and " mod4 a < 4" and  "a =4 mod4 a" by auto
qed

lemma the_equality': "P a \<Longrightarrow>  \<exists>!x. P x \<Longrightarrow> a = (THE x. P x)"
  by (rule sym, auto)

lemma mod4_bestdef_inv: assumes "0\<le> z" "z < 4" "a =4 z" shows "z = mod4 a"
  using eq4_ex_unique by (subst mod4_def, rule_tac the_equality',insert assms, auto)

lemma eqmod4_imp_eq4: assumes "x = mod4 y" shows "x =4 y"
proof-
  have "y =4 mod4 y" by (rule  mod4_bestdef)
  from this have "y =4 x" by (subst(asm) `x = mod4 y`[symmetric])
  then show "x =4 y" by (rule eq4_sym)
qed



lemma assumes "x =4 mod4 y" shows "x =4 y"
oops


lemma eq4_imp_eq: assumes "x =4 y" "0\<le>x\<and>x<4" "0\<le>y\<and>y<4" shows "x = y"
proof -
  from assms(1) have "\<exists>n. x = y + real_of_int (4 * n)" by (subst(asm) eq4_def)
  then obtain n where n_def:"x = y + real_of_int (4 * n)" by (rule exE)
  consider "n=0"|"n\<ge>1"|"n\<le>-1" by linarith
  then show "x=y"
  proof (cases)
    assume "n = 0" from this n_def show "x=y" by auto
  next
    assume "n\<ge>1"
    from this n_def have "x \<ge> y + 4" by fastforce
    from this assms(2,3) have False by linarith
    then show ?thesis ..
  next
    assume "n\<le>-1"
    from this n_def have "x \<le> y - 4" by fastforce
    from this assms(2,3) have False by linarith
    then show ?thesis .. 
  qed
qed   

lemma eq4_swap: "(x+y =4 z) = (x =4 z-y)" "(z-y =4 x) = (z =4 x+y)"
proof -
  show "(x+y =4 z) = (x =4 z-y)"
  proof
  assume "x+y =4 z"
  from this have "\<exists>n. x+y = z + real_of_int (4 * n)" by (subst(asm) eq4_def)
  then obtain n where "x+y = z + real_of_int (4 * n)" by (rule exE) 
  then have "x = z - y + real_of_int (4 * n)" by algebra
  then have "\<exists>n. x = z - y + real_of_int (4 * n)" by blast
  then show "x =4 z-y" by (subst(asm) eq4_def[symmetric])
next 
  assume "x =4 z-y"
  then have "\<exists>n. x = z - y + real_of_int (4 * n)" by (subst(asm) eq4_def) 
  then obtain n where "x = z - y + real_of_int (4 * n)" by (rule exE) 
  then have "x+y = z + real_of_int (4 * n)" by algebra
  from this have "\<exists>n. x+y = z + real_of_int (4 * n)" by blast
  then show "x+y =4 z" by (subst(asm) eq4_def[symmetric])
qed
  then show "(z-y =4 x) = (z =4 x+y)" using eq4_sym by blast
qed

lemma eq4_negmult: assumes "x =4 z" shows "-x =4 -z"
proof -
  from assms have "0+x =4 z" by simp
  then have "0 =4 z -x" by (subst(asm) eq4_swap)
  then have "-z + z =4 z - x" by simp
  then have "-z =4 z - x -z" by (subst(asm) eq4_swap)
  then have "-z =4 -x" by simp
  then show "-x =4 -z" by (rule eq4_sym)
qed

lemma mod4_zero: assumes "mod4 x = 0" shows "mod4 (-x) = 0"
proof -
  have "mod4 (-x) =4 -x" by (rule_tac eq4_sym, rule mod4_bestdef)
  have "x =4 mod4 x" by (rule mod4_bestdef)
  then have "x =4 0" by (subst(asm) assms)
  then have "0+x =4 0" by simp
  then have "0 =4 0 -x" by (subst(asm) eq4_swap)
  then have "-x =4 0" by (rule_tac eq4_sym, simp)
  from this `mod4 (-x) =4 -x` have "mod4 (-x) =4 0" by (rule_tac eq4_trans)
  moreover have "0\<le> mod4 (-x) \<and> mod4 (-x) < 4" using mod4_bestdef by blast
  moreover have "0\<le>(0::real) \<and> (0::real) < 4" by simp
  ultimately show "mod4 (-x) = 0" by (rule eq4_imp_eq)
qed

lemma eq_iff_eq4: assumes "c \<le> a \<and> a < d" "c \<le> b \<and> b < d" "c\<le>d" "d-c \<le> 4" 
                  shows"(a = b) = (a =4 b)"
proof (rule iffI)
  assume "a=b"
  show "a =4 b" by (subst `a = b`, rule eq4_refl)
next
  assume "a =4 b"
  from this obtain n where n_def:"a = b + real_of_int (4 * n)" by (rule_tac exE, subst(asm) eq4_def)
  from this assms have "n=0" by linarith
  from n_def this show "a=b" by simp
qed

lemma mod4_eq4: "(mod4 a = mod4 b) = (a =4 b)"
proof (rule iffI)
  assume "mod4 a = mod4 b"
  then have "mod4 a =4 b" by (rule eqmod4_imp_eq4)
  then have "b =4 mod4 a" by (rule eq4_sym)
  have "a =4 mod4 a" by (rule mod4_bestdef)
  then have "mod4 a =4 a" by (rule eq4_sym)
  from `b =4 mod4 a` this have "b =4 a" by (rule eq4_trans)
  then show "a =4 b" by (rule eq4_sym)
next
  assume "a =4 b"
  have "a =4 mod4 a" by (rule mod4_bestdef)
  then have "mod4 a =4 a" by (rule eq4_sym)
  from this `a =4 b` have "mod4 a =4 b" by (rule eq4_trans)  
  have "b =4 mod4 b" by (rule mod4_bestdef)
  from `mod4 a =4 b` this have "mod4 a =4 mod4 b" by (rule eq4_trans)
  have "0\<le> mod4 a \<and> mod4 a < 4"  "0\<le> mod4 b \<and> mod4 b < 4" using mod4_bestdef by auto
  from `mod4 a =4 mod4 b` `0\<le> mod4 a \<and> mod4 a < 4` `0\<le> mod4 b \<and> mod4 b < 4` 
  show "mod4 a = mod4 b" by (rule eq4_imp_eq)
qed

lemma mod4_neg: "mod4 (-x) = mod4 (- (mod4 x))"
proof -
  have "x =4 mod4 x" by (rule mod4_bestdef)
  then have "-x =4 - (mod4 x)" by (rule eq4_negmult)
  then show "mod4 (-x) = mod4 (- (mod4 x))" by (subst mod4_eq4)
qed

lemma mod4_projection_property: "mod4 x = mod4 (mod4 x)"
proof -
  have "x =4 mod4 x" by (rule mod4_bestdef)
  then show "mod4 x = mod4 (mod4 x)" by (subst mod4_eq4)
qed

lemma mod4_abs: "mod4 \<bar>x\<bar> = mod4 x \<or> mod4 \<bar>x\<bar> = mod4 (-x)"
  using abs_real_def by presburger

lemma mod4_neg_eq: "(mod4 x = mod4 y) = (mod4 (-x) = mod4 (-y))"
proof
  assume "mod4 x = mod4 y"
  then have "-mod4 x = - mod4 y" by (rule arg_cong)
  then have "mod4 (-mod4 x) = mod4 (- mod4 y)" by (rule arg_cong)
  then show "mod4 (-x) = mod4 (-y)" by (subst mod4_neg,subst mod4_neg)
next
  assume "mod4 (-x) = mod4 (-y)"
  then have "-mod4 (-x) = - mod4 (-y)" by (rule arg_cong)
  then have "mod4 (-mod4 (-x)) = mod4 (- mod4 (-y))" by (rule arg_cong)
  then have "mod4 (-(-x)) = mod4 (-(-y))" by (subst mod4_neg,subst mod4_neg)
  then show "mod4 x = mod4 y" by simp
qed

lemma eq4_neg_eq: "(x =4 y) = (-x =4 -y)"
proof -
  have "(x =4 y) = (mod4 x = mod4 y)" by (rule mod4_eq4[symmetric])
  also have "(mod4 x = mod4 y) = (mod4 (-x) = mod4 (-y))" by (rule mod4_neg_eq)
  finally show ?thesis using mod4_eq4 by simp
qed

lemma eq4_abs: assumes "\<bar>x\<bar> =4 \<bar>y\<bar>" shows "min (mod4 x) (mod4 (-x)) = min (mod4 y) (mod4 (-y))"
proof -
  from assms have "mod4 \<bar>x\<bar> = mod4 \<bar>y\<bar>" by (subst(asm) mod4_eq4[symmetric])
  from this mod4_abs consider "mod4 x = mod4 y" | "mod4 (-x) = mod4 y" |
                        "mod4 (-x) = mod4 (-y)" | "mod4 x = mod4 (-y)"
    by linarith
  then show ?thesis
  proof (cases)
    assume "mod4 x = mod4 y"
    then have "mod4 (-x) = mod4 (-y)" by (subst(asm) mod4_neg_eq)
    show "min (mod4 x) (mod4 (-x)) = min (mod4 y) (mod4 (-y))" 
      by (subst `mod4 (-x) = mod4 (-y)`, subst `mod4 x = mod4 y`, rule refl)
  next
    assume "mod4 (-x) = mod4 (-y)"
    then have "mod4 x = mod4 y" by (subst mod4_neg_eq)
    show "min (mod4 x) (mod4 (-x)) = min (mod4 y) (mod4 (-y))" 
      by (subst `mod4 (-x) = mod4 (-y)`, subst `mod4 x = mod4 y`, rule refl)
  next
    assume "mod4 (-x) = mod4 y"
    then have "mod4 (-(-x)) = mod4 (-y)" by (subst(asm) mod4_neg_eq)
    then have "mod4 x = mod4 (-y)" by simp
    show "min (mod4 x) (mod4 (-x)) = min (mod4 y) (mod4 (-y))" 
      by (subst `mod4 (-x) = mod4 y`, subst `mod4 x = mod4 (-y)`,rule min.commute)
  next
    assume "mod4 x = mod4 (-y)"
    then have "mod4 (-x) = mod4 (-(-y))" by (subst(asm) mod4_neg_eq)
    then have "mod4 (-x) = mod4 y" by simp
    show "min (mod4 x) (mod4 (-x)) = min (mod4 y) (mod4 (-y))" 
      by (subst `mod4 (-x) = mod4 y`, subst `mod4 x = mod4 (-y)`,rule min.commute)
  qed
qed

lemma mod4_simple: assumes "0 \<le> x \<and> x < 4" shows "mod4 x = x"
proof (rule eq4_imp_eq)
  show "mod4 x =4 x" by (rule eq4_sym,rule mod4_bestdef(3))
  show "0 \<le> mod4 x \<and> mod4 x < 4" using mod4_bestdef by simp
  from assms show "0 \<le> x \<and> x < 4" by -
qed

lemma eq4_imp_eq_mod4: assumes "0 \<le> y \<and> y < 4" "x =4 y" shows "mod4 x = y"
proof -
  from assms(2) have "mod4 x = mod4 y" by (subst mod4_eq4)
  from assms(1) have "mod4 y = y" by (rule mod4_simple)
  from `mod4 x = mod4 y` this show "mod4 x = y" by (rule trans)
qed 

lemma eq4_imp_eq_mod4_0: assumes "x =4 0" shows "mod4 x = 0"
proof-
  have "0 \<le> (0::real) \<and> (0::real) < 4" by linarith
  from this assms show ?thesis by (rule  eq4_imp_eq_mod4)
qed

lemma eq_mod4_imp_eq4: assumes "mod4 x = y" shows "x =4 y"
  using assms mod4_bestdef(3) by blast

lemma min_mod4_eq4: assumes "(min (mod4 x) (mod4 y)) = z" shows "(min (mod4 x) (mod4 y)) =4 z"
proof -
  have "0 \<le> mod4 x" and "mod4 x < 4" by (rule_tac [!] mod4_bestdef)
  moreover have "0 \<le> mod4 y" and "mod4 y < 4" by (rule_tac [!] mod4_bestdef)
  ultimately have "0 \<le> z" and "z < 4" using assms by linarith+
  then have "z =4 z" using mod4_simple eqmod4_imp_eq4
    by metis
  from this `(min (mod4 x) (mod4 y)) = z` show "(min (mod4 x) (mod4 y)) =4 z" by simp
qed

lemma min_mod4_eq: assumes "0\<le>z \<and> z<4" "(min (mod4 x) (mod4 y)) =4 z" shows "(min (mod4 x) (mod4 y)) = z"
proof -
  have "0 \<le> mod4 x" and "mod4 x < 4" by (rule_tac [!] mod4_bestdef)
  moreover have "0 \<le> mod4 y" and "mod4 y < 4" by (rule_tac [!] mod4_bestdef)
  ultimately have "0 \<le> min (mod4 x) (mod4 y) \<and> min (mod4 x) (mod4 y) < 4" by linarith
  from this assms show "(min (mod4 x) (mod4 y)) = z" by (rule_tac eq4_imp_eq)
qed

lemma min_mod4_eq4_eq: assumes "0\<le>z \<and> z<4" shows "((min (mod4 x) (mod4 y)) =4 z) = ((min (mod4 x) (mod4 y)) = z)"
  using min_mod4_eq min_mod4_eq4 assms by blast

lemma eq4_4_0: "4 =4 0" 
  by (simp add: eq4_def)

lemma mod4_2_inv[simp]: "mod4( - 2) = 2"
proof -
  have "-2 =4 2"
    by (rule eq4_sym, simp add: eq4_def)
  moreover have "0\<le>(2::real) \<and> (2::real)<4" by linarith
  ultimately show ?thesis
    using mod4_bestdef_inv by metis
qed

lemma eq4_2_inv: "- 2 =4 2"
proof - 
  from mod4_2_inv[symmetric] have "2 =4 -2" by (rule eqmod4_imp_eq4)
  then show ?thesis by (rule eq4_sym)
qed

lemma mod4_min_projection_property: "(min (mod4 x) (mod4 y)) = mod4 (min (mod4 x) (mod4 y))"
proof -
  consider "(min (mod4 x) (mod4 y)) = (mod4 x)" | "(min (mod4 x) (mod4 y)) = (mod4 y)"
    by linarith
  then show ?thesis proof (cases)
    assume case1: "min (mod4 x) (mod4 y) = mod4 x"
    also have "... = mod4 (mod4 x)" by (rule mod4_projection_property)
    finally show "min (mod4 x) (mod4 y) = mod4(min (mod4 x) (mod4 y))" by (subst case1, auto)
  next
    assume case2: "min (mod4 x) (mod4 y) = mod4 y"
    also have "... = mod4 (mod4 y)" by (rule mod4_projection_property)
    finally show "min (mod4 x) (mod4 y) = mod4(min (mod4 x) (mod4 y))" by (subst case2, auto)
  qed
qed

lemma mod4_inv:"(mod4 x) + (mod4 (-x)) =4 0"
proof -
  have "mod4 x = mod4 (-(-x))" by simp
  then have "mod4 (mod4 x) = mod4 (-(mod4 (-x)))" using mod4_projection_property mod4_neg by simp
  then have "(mod4 x) =4 0 -(mod4 (-x))" using mod4_eq4 by auto
  then show ?thesis  by (subst eq4_swap)
qed

lemma min_mod4_difference_bounds:
"0 \<le> (min (mod4 (x-y)) (mod4 (y-x))) \<and> (min (mod4 (x-y)) (mod4 (y-x))) \<le> 2"
proof -
  have "(mod4 (x-y)) < 4" using mod4_bestdef
    by presburger
  have "(mod4 (-(x-y))) < 4" using mod4_bestdef
    by presburger
  have "mod4 (x-y) \<le> 2 \<or> mod4 (-(x-y)) \<le> 2"
  proof (rule ccontr, subst(asm) de_Morgan_disj, (subst(asm) not_le)+, erule conjE) 
    assume "2 < mod4 (x - y) " "2 < mod4 (- (x-y))" 
    then have "4< mod4 (x - y) + mod4 (- (x-y)) \<and> mod4 (x - y) + mod4 (- (x-y)) < 8" 
      using `(mod4 (-(x-y))) < 4` `(mod4 (x-y)) < 4` by force    
    then have "\<not>(mod4 (x - y) + mod4 (- (x-y)) =4 0)" using eq4_def by auto
    from this mod4_inv show False by contradiction
  qed
  from this mod4_bestdef show ?thesis by force
qed

lemma delete_mod4: "(mod4 x + y =4 z) = (x + y =4 z)" 
proof 
  assume "mod4 x + y =4 z"
  have "x =4 mod4 x" by (rule mod4_bestdef)
  moreover from `mod4 x + y =4 z` have "mod4 x =4 z - y" by (subst (asm) eq4_swap)
  ultimately have "x =4 z - y" by (rule eq4_trans)
  then show "x + y =4 z"  by (subst eq4_swap)
next 
  assume "x + y =4 z"
  have "mod4 x =4 x" by (simp add: mod4_bestdef eq4_sym)
  moreover from `x + y =4 z` have "x =4 z - y" by (subst (asm) eq4_swap)
  ultimately have "mod4 x =4 z - y" by (rule eq4_trans)
  then show "mod4 x + y =4 z"  by (subst eq4_swap)
qed
end