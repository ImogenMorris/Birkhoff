theory Bijection_on_Mono_on imports Complex_Main

begin


definition mono_on :: "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool"
  where "mono_on f S = (\<forall>x\<in>S. \<forall>y\<in>S. x < y \<longrightarrow> f x < f y)"

definition inv_on :: "real set \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real)"
  where "inv_on S f = (\<lambda>y. SOME x. x \<in> S \<and> f x = y)"

lemma bij_betw_inv_on: assumes "bij_betw f A B" shows "(inv_on A f) ` B = A"
proof (subst inv_on_def, subst image_def, rule)
  have "inj_on f A" and "f ` A = B" using assms
    by (auto simp add: bij_betw_def)
  from `image f A = B`
  have aset: "\<forall>b \<in> B. \<exists>a. a \<in> A \<and> f a = b" using image_def by blast
  then have some_prop: 
"\<forall>b \<in> B. (SOME a. a \<in> A \<and> f a = b) \<in> A \<and> f (SOME a. a \<in> A \<and> f a = b) = b"
    by (subst(asm) some_eq_ex[symmetric])
  then show "{y. \<exists>x\<in>B. y = (SOME a. a \<in> A \<and> f a = x)} \<subseteq> A" by blast
  show "A \<subseteq> {y. \<exists>x\<in>B. y = (SOME a. a \<in> A \<and> f a = x)}" 
  proof (rule, rule, rule_tac x = "f x" in bexI, rule some1_equality[symmetric, rotated]
, rule conjI, assumption, rule, rule_tac a = "x" in ex1I, rule conjI, assumption, rule)
    fix y assume "y \<in> A"
    from this `image f A = B`
    show "f y \<in> B" using image_def by blast
    fix x
    assume "x \<in> A \<and> f x = f y" 
    then show "x = y" using `inj_on f A` inj_on_def `y \<in> A` by metis
  qed
qed
thm bij_betw_def
lemma bij_betw_inv_on: assumes "bij_betw f A B" shows "inj_on (inv_on A f) B"
  oops
  thm inj_on_def inv_on_def image_def
lemma inv_on_in_set: assumes "(inv_on A f) ` B = A" "y \<in> B"
  shows "inv_on A f y \<in> A" 
  using assms(1) assms(2) by blast

lemma assumes "bij_betw f A B" "y \<in> A" shows "f y \<in> B"
  using assms(1) assms(2) bij_betwE by blast

thm bij_betw_def
lemma image_inv_on_welldefined: assumes "f ` A = B" "y \<in> B" shows "f (inv_on A f y) = y" "(inv_on A f y) \<in> A"
proof (subst inv_on_def)
  from assms(1) have "{y. \<exists>x\<in>A. y = f x} = B" 
    by (subst (asm) image_def)
  from this `y \<in> B` have "\<exists>x. x\<in>A \<and> f x = y" by blast
  then have something:"(SOME x. x\<in>A \<and> f x = y) \<in>A \<and> f (SOME x. x\<in>A \<and> f x = y) = y" by (rule someI_ex)
  from this show "f (SOME x. x \<in> A \<and> f x = y) = y" by (rule conjunct2)
  from something show "inv_on A f y \<in> A" by (subst inv_on_def, rule_tac conjunct1)
qed

lemma image_inv_on_welldefined_sym: 
  assumes "inj_on f A" "y \<in> A" shows "(inv_on A f) (f y) = y" "(inv_on A f) (f y)\<in> A"
proof (subst inv_on_def)
  from assms(1) have inj:"\<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y" 
    by (subst (asm) inj_on_def)
  thm inj_on_def
  from `y \<in> A` have "\<exists>x. x \<in>A \<and> f x = f y" by blast
  then have something:"(SOME x. x\<in>A \<and> f x = f y) \<in> A \<and> f (SOME x. x\<in>A \<and> f x = f y) = f y"
    by (rule someI_ex)
  from this have "(SOME x. x\<in>A \<and> f x = f y) \<in> A \<and> (SOME x. x\<in>A \<and> f x = f y) =  y"
    using inj`y \<in> A` by blast
  from this show "(SOME x. x \<in> A \<and> f x = f y) = y" by (rule conjunct2)
  from something show "(inv_on A f) (f y)\<in> A" by (subst inv_on_def, rule_tac conjunct1)
qed

lemma bij_betw_inv_on_welldefined:assumes "bij_betw f A B" "y \<in> B" 
  shows "f (inv_on A f y) = y" "(inv_on A f y) \<in> A"
  using assms(1,2)  bij_betw_def image_inv_on_welldefined 
  by  metis +

lemma bij_betw_inv_on_welldefined_sym:assumes "bij_betw f A B" "y \<in> A" 
  shows "(inv_on A f) (f y) = y" "(inv_on A f) (f y)\<in> A"
  using assms(1,2)  bij_betw_def image_inv_on_welldefined_sym by metis+

lemma assumes "bij_betw f A B" shows "bij_betw (inv_on A f) B A" oops


lemma mono_on_bij_betw_mono_inv_on: assumes "mono_on f A" "bij_betw f A B" shows "mono_on (inv_on A f) B"
proof (subst mono_on_def, safe, rule ccontr)
  fix x y assume "x \<in> B" "y \<in> B" "x < y" "\<not> inv_on A f x < inv_on A f y"
  then consider "inv_on A f x = inv_on A f y" | "inv_on A f x > inv_on A f y" by linarith
  then show False
  proof (cases)
    assume "inv_on A f y < inv_on A f x"
    from `bij_betw f A B` have "(inv_on A f) ` B = A" by (rule bij_betw_inv_on)
    from this `y \<in> B` `x \<in> B` have "inv_on A f y \<in> A" and "inv_on A f x \<in> A" 
      by (auto simp add: inv_on_in_set)
    from this `inv_on A f y < inv_on A f x`
    have "f (inv_on A f y) < f (inv_on A f x)" 
      using `mono_on f A` mono_on_def by blast
    from this bij_betw_inv_on_welldefined(1) have "y<x"
      using \<open>x \<in> B\<close> \<open>y \<in> B\<close> assms(2) by fastforce
    from this `x < y` show False by linarith
  next
    assume "inv_on A f x = inv_on A f y"
    from this
    have "f (inv_on A f x) = f (inv_on A f y)" 
      by (rule arg_cong)
    from this bij_betw_inv_on_welldefined(1) have "x = y"
      using \<open>x \<in> B\<close> \<open>y \<in> B\<close> assms(2) by fastforce
    from this `x < y` show False by linarith
  qed
qed
  
  thm mono_on_def
(* but we would like mono_on and bij_on because total functions*)
(*note cannot use mono and must use mono_on*)
lemma mono_bij_cont_open_univ: assumes mono_f:"mono_on f {x. (a::real) < x \<and> x < b}" (is "mono_on f ?ab")
  and bij_f:"bij_betw f {x. (a::real) < x \<and> x < b} (UNIV::real set)" 
shows "\<forall>x \<in> {x. (a::real) < x \<and> x < b}. isCont f x"
proof (subst isCont_def, subst LIM_def, (subst dist_real_def) +, safe)
  fix r eps assume "a < r"  "r < b" and eps_def: "eps > (0::real)"
  thm bij_betw_def image_def
  from this have "r \<in> ?ab" by simp
  from bij_f obtain q where q_def:"f r + eps = f q" and "q \<in> ?ab"
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from bij_f obtain p where p_def:"f r - eps = f p" and "p \<in> ?ab"
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
(*want f r > f p > f 0

consider eps < f r that's enough*)
  from mono_f bij_f have "mono_on (inv_on ?ab f) UNIV" 
    by (rule mono_on_bij_betw_mono_inv_on)
  from q_def eps_def have "f q > f r" by linarith
  from p_def eps_def have "f p < f r" by linarith
  show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps"
  proof (rule exI, safe)
    show "min (q-r) (r-p )>0" 
    proof -
      from `f q > f r` `mono_on (inv_on ?ab f) UNIV`
      have inv_fq_fr:"(inv_on ?ab f) (f q) > (inv_on ?ab f) (f r)" 
        using mono_on_def 
        by simp 
      from bij_f `q \<in> ?ab` have "(inv_on ?ab f) (f q) = q"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      moreover from bij_f `r \<in> ?ab` have "(inv_on ?ab f) (f r) = r"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      ultimately have "q > r" using inv_fq_fr by simp
      from `f p < f r` `mono_on (inv_on ?ab f) UNIV`
      have inv_fq_fr:"(inv_on ?ab f) (f p) < (inv_on ?ab f) (f r)" 
        using mono_on_def 
        by simp 
      from bij_f `p \<in> ?ab` have "(inv_on ?ab f) (f p) = p"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      moreover from bij_f `r \<in> ?ab` have "(inv_on ?ab f) (f r) = r"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      ultimately have "p < r" using inv_fq_fr by simp
      from `q > r` `p < r`
      show "min (q-r) (r-p )>0" by simp
    qed
 (*   from this reals_Archimedean3 obtain n where "(n::nat)*(q-r) > a"
      by blast*) 
    fix x
    assume "x \<noteq> r" "\<bar>x - r\<bar> < min (q-r) (r-p )"
    from q_def have "eps = f q - f r" by simp
    
    from `x \<noteq> r` consider "x - r >0" |"x - r <0" by linarith
    then show "\<bar>f x - f r\<bar> < eps" 
    proof (cases) 
      assume "0 < x - r"
      then have "x > r" by linarith
      from this `\<bar>x - r\<bar> < min (q-r) (r-p )` have "x < q" by linarith
      from this `q \<in> ?ab` `x > r` `r \<in> ?ab` have "x \<in> ?ab" by simp
      from this `x > r` `r \<in> ?ab`  have "f x > f r" 
        using `mono_on f ?ab` mono_on_def by simp
      from `x \<in> ?ab``x < q` `q \<in> ?ab`  have "f q > f x" 
        using `mono_on f ?ab` mono_on_def by simp
      from this q_def `f x > f r` show "\<bar>f x - f r\<bar> < eps" by linarith
    next
       assume "0 > x - r"
       then have "x < r" by linarith 
      from this `\<bar>x - r\<bar> < min (q-r) (r-p)` have "x < q" by linarith 
      from `x < r` `\<bar>x - r\<bar> < min (q-r) (r-p )` have "x >p" by linarith 
      from this `p \<in> ?ab` `x < r` `r \<in> ?ab` have "x \<in> ?ab" by simp
      from this `x >p` `p \<in> ?ab`  have "f x > f p" 
        using `mono_on f ?ab` mono_on_def by simp
      from `x \<in> ?ab``x < q` `q \<in> ?ab`  have "f q > f x" 
        using `mono_on f ?ab` mono_on_def by simp
      from this `f x > f p` q_def p_def  
      show "\<bar>f x - f r\<bar> < eps" by linarith
    qed
  qed
qed
(*but it may not be continuous at the edge?*)
(*proof (rule ccontr)
  assume not_cont_f:"\<not> (\<forall>x \<in> {x. (a::real) < x \<and> x < b}. isCont f x)"
  from bij_f have "f ` {x. (a::real) < x \<and> x < b} = {y. \<exists>x\<in>{x. (a::real) < x \<and> x < b}. y = f x}"
    using bij_betw_def image_def by blast
  from bij_f have "f ` {x. (a::real) < x \<and> x < b} = (UNIV::real set)" 
    by (subst (asm) bij_betw_def, blast)
  then have "\<forall>y. \<exists>x\<in>{x. (a::real) < x \<and> x < b}. y = f x" by blast
  from not_cont_f
  have "\<not> (\<forall>x \<in> {x. (a::real) < x \<and> x < b}. 
(\<forall>r>0. \<exists>s>0. \<forall>z. z \<noteq> x \<and> dist z x < s \<longrightarrow> dist (f z) (f x) < r))"
    by (subst (asm) isCont_def, subst (asm) LIM_def)
  from  this
  have "\<exists>x \<in> {x. (a::real) < x \<and> x < b}. " *)
lemma  small_epsilon: assumes mono_f:"mono_on f {x. (a::real) < x \<and> x < b}" 
  and bij_f:"bij_betw f {x. (a::real) < x \<and> x < b} {x. c< x \<and> x < (d::real)}" (is "bij_betw f ?ab ?cd")
  and fpluseps:"(f r + eps) \<in> {x. c< x \<and> x < (d::real)}" and  "f r \<in> {x. c< x \<and> x < (d::real)}"
 and fminuseps: "(f r - eps) \<in> {x. c< x \<and> x < (d::real)}"
 and r_def:"r\<in>{x. (a::real) < x \<and> x < b}" and eps_def: "eps > (0::real)"
shows "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps "
proof-  
  from bij_f fpluseps obtain q where q_def:"f r + eps = f q" and "q \<in> ?ab"
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from this bij_f have "f q \<in> ?cd" 
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from bij_f fminuseps obtain p where p_def:"f r - eps = f p" and "p \<in> ?ab"
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from this bij_f have "f p \<in> ?cd" 
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from mono_f bij_f have "mono_on (inv_on ?ab f) {x. c< x \<and> x < (d::real)}" 
    by (rule mono_on_bij_betw_mono_inv_on)
  from q_def eps_def have "f q > f r" by linarith
  from p_def eps_def have "f p < f r" by linarith
  show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps"
  proof (rule exI, safe)
    show "min (q-r) (r-p )>0" 
    proof -
      from `f q \<in> ?cd` `f r \<in> ?cd` `mono_on (inv_on ?ab f) {x. c< x \<and> x < (d::real)}`
      have inv_fq_fr:"(inv_on ?ab f) (f q) > (inv_on ?ab f) (f r)" 
        by (simp add: \<open>f r < f q\<close>  mono_on_def)   
      from bij_f `q \<in> ?ab` have "(inv_on ?ab f) (f q) = q"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      moreover from bij_f `r \<in> ?ab` have "(inv_on ?ab f) (f r) = r"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      ultimately have "q > r" using inv_fq_fr by simp
      from `f p < f r` `f p \<in> ?cd` `f r \<in> ?cd` `mono_on (inv_on ?ab f) {x. c< x \<and> x < (d::real)}`
      have inv_fq_fr:"(inv_on ?ab f) (f p) < (inv_on ?ab f) (f r)" 
        using mono_on_def 
        by simp 
      from bij_f `p \<in> ?ab` have "(inv_on ?ab f) (f p) = p"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      moreover from bij_f `r \<in> ?ab` have "(inv_on ?ab f) (f r) = r"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      ultimately have "p < r" using inv_fq_fr by simp
      from `q > r` `p < r`
      show "min (q-r) (r-p )>0" by simp
    qed 
    fix x
    assume "x \<noteq> r" "\<bar>x - r\<bar> < min (q-r) (r-p )"
    from q_def have "eps = f q - f r" by simp    
    from `x \<noteq> r` consider "x - r >0" |"x - r <0" by linarith
    then show "\<bar>f x - f r\<bar> < eps" 
    proof (cases) 
      assume "0 < x - r"
      then have "x > r" by linarith
      from this `\<bar>x - r\<bar> < min (q-r) (r-p )` have "x < q" by linarith
      from this `q \<in> ?ab` `x > r` `r \<in> ?ab` have "x \<in> ?ab" by simp
      from this `x > r` `r \<in> ?ab`  have "f x > f r" 
        using `mono_on f ?ab` mono_on_def by simp
      from `x \<in> ?ab``x < q` `q \<in> ?ab`  have "f q > f x" 
        using `mono_on f ?ab` mono_on_def by simp
      from this q_def `f x > f r` show "\<bar>f x - f r\<bar> < eps" by linarith
    next
       assume "0 > x - r"
       then have "x < r" by linarith 
      from this `\<bar>x - r\<bar> < min (q-r) (r-p)` have "x < q" by linarith 
      from `x < r` `\<bar>x - r\<bar> < min (q-r) (r-p )` have "x >p" by linarith 
      from this `p \<in> ?ab` `x < r` `r \<in> ?ab` have "x \<in> ?ab" by simp
      from this `x >p` `p \<in> ?ab`  have "f x > f p" 
        using `mono_on f ?ab` mono_on_def by simp
      from `x \<in> ?ab``x < q` `q \<in> ?ab`  have "f q > f x" 
        using `mono_on f ?ab` mono_on_def by simp
      from this `f x > f p` q_def p_def  
      show "\<bar>f x - f r\<bar> < eps" by linarith
    qed
  qed
qed 

lemma mono_bij_cont_open_open: assumes mono_f:"mono_on f {x. (a::real) < x \<and> x < b}" 
  and bij_f:"bij_betw f {x. (a::real) < x \<and> x < b} {x. c< x \<and> x < (d::real)}" (is "bij_betw f ?ab ?cd")
shows "\<forall>x \<in> {x. (a::real) < x \<and> x < b}. isCont f x"
proof (subst isCont_def, subst LIM_def, (subst dist_real_def) +, safe)
  fix r eps assume r_def: "a < r"  "r < b" and eps_def: "eps > (0::real)"
  thm bij_betw_def image_def
  from r_def have "r \<in> ?ab" by simp
  from bij_f this have "f r \<in> ?cd" by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps "
  proof (cases "(f r + eps) \<in> ?cd \<and> (f r - eps) \<in> ?cd")
    assume "(f r + eps) \<in> ?cd \<and> (f r - eps) \<in> ?cd"
    then have "(f r + eps) \<in> ?cd"  "(f r - eps) \<in> ?cd" by blast+
    from this assms `r \<in> ?ab` `f r \<in> ?cd` eps_def
    show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps"
      by (rule_tac small_epsilon)
  next
    assume "\<not>((f r + eps) \<in> ?cd \<and> (f r - eps) \<in> ?cd)"
    have "(f r + (min \<bar>f r - c\<bar> \<bar>f r - d\<bar>)/ 2) \<in> ?cd" (is "(f r + ?smalleps) \<in> ?cd")
    proof(rule)
      have "\<bar>f r - c\<bar> / 2 > 0" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by auto
      moreover have "f r > c" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by simp
      ultimately have c_less:"c < f r + \<bar>f r - c\<bar> / 2" by argo
      have "f r < d" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by simp
      then have d_gr:"f r + \<bar>f r - d\<bar> / 2 < d" by argo
      from c_less d_gr 
      show "c < f r + min \<bar>f r - c\<bar> \<bar>f r - d\<bar> / 2 \<and> f r + min \<bar>f r - c\<bar> \<bar>f r - d\<bar> / 2 < d" by argo
    qed
    moreover have "(f r - (min \<bar>f r - c\<bar> \<bar>f r - d\<bar>)/ 2) \<in> ?cd" 
    proof(rule)
      have "\<bar>f r - c\<bar> / 2 > 0" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by auto
      moreover have "f r > c" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by simp
      ultimately have c_less:"c < f r + \<bar>f r - c\<bar> / 2" by argo
      have "f r < d" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by simp
      then have d_gr:"f r + \<bar>f r - d\<bar> / 2 < d" by argo
      from c_less d_gr 
      show "c < f r - min \<bar>f r - c\<bar> \<bar>f r - d\<bar> / 2 \<and> f r - min \<bar>f r - c\<bar> \<bar>f r - d\<bar> / 2 < d" by argo
    qed
    ultimately have smalleps_cd:"(f r + ?smalleps) \<in> ?cd" "(f r - ?smalleps) \<in> ?cd" by blast+
    have "?smalleps > 0" using zero_less_abs_iff `f r \<in> ?cd` by auto
    from `\<not>((f r + eps) \<in> ?cd \<and> (f r - eps) \<in> ?cd)` this have "?smalleps < eps"
      using smalleps_cd `?smalleps > 0` eps_def  `f r \<in> ?cd` by auto
    from `?smalleps > 0` assms `r \<in> ?ab` `f r \<in> ?cd` `(f r + ?smalleps) \<in> ?cd` `(f r - ?smalleps) \<in> ?cd`
    have "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < ?smalleps"
      by (rule_tac small_epsilon)
    then obtain del where "del>0" and del_def:"\<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < ?smalleps"
      by blast
    have "\<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps"
    proof (safe)
      fix x
      assume "x \<noteq> r" "\<bar>x - r\<bar> < del"
      from this del_def have "\<bar>f x - f r\<bar> < ?smalleps"
        by blast
      from this `?smalleps < eps` show "\<bar>f x - f r\<bar> < eps" by linarith
    qed
    from this `del>0` show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps" 
      by blast
  qed
qed

lemma  small_epsilon_inf: assumes mono_f:"mono_on f {x. (a::real) < x}" 
  and bij_f:"bij_betw f {x. (a::real) < x} {x. c< x \<and> x < (d::real)}" (is "bij_betw f ?ab ?cd")
  and fpluseps:"(f r + eps) \<in> {x. c< x \<and> x < (d::real)}" and  "f r \<in> {x. c< x \<and> x < (d::real)}"
 and fminuseps: "(f r - eps) \<in> {x. c< x \<and> x < (d::real)}"
 and r_def:"r\<in>{x. (a::real) < x}" and eps_def: "eps > (0::real)"
shows "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps "
proof-  
  from bij_f fpluseps obtain q where q_def:"f r + eps = f q" and "q \<in> ?ab"
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from this bij_f have "f q \<in> ?cd" 
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from bij_f fminuseps obtain p where p_def:"f r - eps = f p" and "p \<in> ?ab"
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from this bij_f have "f p \<in> ?cd" 
    by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  from mono_f bij_f have "mono_on (inv_on ?ab f) {x. c< x \<and> x < (d::real)}" 
    by (rule mono_on_bij_betw_mono_inv_on)
  from q_def eps_def have "f q > f r" by linarith
  from p_def eps_def have "f p < f r" by linarith
  show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps"
  proof (rule exI, safe)
    show "min (q-r) (r-p )>0" 
    proof -
      from `f q \<in> ?cd` `f r \<in> ?cd` `mono_on (inv_on ?ab f) {x. c< x \<and> x < (d::real)}`
      have inv_fq_fr:"(inv_on ?ab f) (f q) > (inv_on ?ab f) (f r)" 
        by (simp add: \<open>f r < f q\<close>  mono_on_def)   
      from bij_f `q \<in> ?ab` have "(inv_on ?ab f) (f q) = q"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      moreover from bij_f `r \<in> ?ab` have "(inv_on ?ab f) (f r) = r"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      ultimately have "q > r" using inv_fq_fr by simp
      from `f p < f r` `f p \<in> ?cd` `f r \<in> ?cd` `mono_on (inv_on ?ab f) {x. c< x \<and> x < (d::real)}`
      have inv_fq_fr:"(inv_on ?ab f) (f p) < (inv_on ?ab f) (f r)" 
        using mono_on_def 
        by simp 
      from bij_f `p \<in> ?ab` have "(inv_on ?ab f) (f p) = p"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      moreover from bij_f `r \<in> ?ab` have "(inv_on ?ab f) (f r) = r"
        by (rule bij_betw_inv_on_welldefined_sym(1))
      ultimately have "p < r" using inv_fq_fr by simp
      from `q > r` `p < r`
      show "min (q-r) (r-p )>0" by simp
    qed 
    fix x
    assume "x \<noteq> r" "\<bar>x - r\<bar> < min (q-r) (r-p )"
    from q_def have "eps = f q - f r" by simp    
    from `x \<noteq> r` consider "x - r >0" |"x - r <0" by linarith
    then show "\<bar>f x - f r\<bar> < eps" 
    proof (cases) 
      assume "0 < x - r"
      then have "x > r" by linarith
      from this `\<bar>x - r\<bar> < min (q-r) (r-p )` have "x < q" by linarith
      from this `q \<in> ?ab` `x > r` `r \<in> ?ab` have "x \<in> ?ab" by simp
      from this `x > r` `r \<in> ?ab`  have "f x > f r" 
        using `mono_on f ?ab` mono_on_def by simp
      from `x \<in> ?ab``x < q` `q \<in> ?ab`  have "f q > f x" 
        using `mono_on f ?ab` mono_on_def by simp
      from this q_def `f x > f r` show "\<bar>f x - f r\<bar> < eps" by linarith
    next
       assume "0 > x - r"
       then have "x < r" by linarith 
      from this `\<bar>x - r\<bar> < min (q-r) (r-p)` have "x < q" by linarith 
      from `x < r` `\<bar>x - r\<bar> < min (q-r) (r-p )` have "x >p" by linarith 
      from this `p \<in> ?ab` `x < r` `r \<in> ?ab` have "x \<in> ?ab" by simp
      from this `x >p` `p \<in> ?ab`  have "f x > f p" 
        using `mono_on f ?ab` mono_on_def by simp
      from `x \<in> ?ab``x < q` `q \<in> ?ab`  have "f q > f x" 
        using `mono_on f ?ab` mono_on_def by simp
      from this `f x > f p` q_def p_def  
      show "\<bar>f x - f r\<bar> < eps" by linarith
    qed
  qed
qed

(*does it at all depend on what ?ab is? If it could be any subset of reals, change it to be such!
Or in the lemma at least*)
lemma mono_bij_cont_openinf_open: assumes mono_f:"mono_on f {x. (a::real) < x}" 
  and bij_f:"bij_betw f {x. (a::real) < x} {x. c< x \<and> x < (d::real)}" (is "bij_betw f ?ab ?cd")
shows "\<forall>x \<in> {x. (a::real) < x}. isCont f x"
proof (subst isCont_def, subst LIM_def, (subst dist_real_def) +, safe)
  fix r eps assume r_def: "a < r" and eps_def: "eps > (0::real)"
  thm bij_betw_def image_def
  from r_def have "r \<in> ?ab" by simp
  from bij_f this have "f r \<in> ?cd" by (subst (asm) bij_betw_def, subst (asm) image_def, blast)
  show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps "
  proof (cases "(f r + eps) \<in> ?cd \<and> (f r - eps) \<in> ?cd")
    assume "(f r + eps) \<in> ?cd \<and> (f r - eps) \<in> ?cd"
    then have "(f r + eps) \<in> ?cd"  "(f r - eps) \<in> ?cd" by blast+
    from this assms `r \<in> ?ab` `f r \<in> ?cd` eps_def
    show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps"
      by (rule_tac small_epsilon_inf)
  next
    assume "\<not>((f r + eps) \<in> ?cd \<and> (f r - eps) \<in> ?cd)"
    have "(f r + (min \<bar>f r - c\<bar> \<bar>f r - d\<bar>)/ 2) \<in> ?cd" (is "(f r + ?smalleps) \<in> ?cd")
    proof(rule)
      have "\<bar>f r - c\<bar> / 2 > 0" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by auto
      moreover have "f r > c" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by simp
      ultimately have c_less:"c < f r + \<bar>f r - c\<bar> / 2" by argo
      have "f r < d" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by simp
      then have d_gr:"f r + \<bar>f r - d\<bar> / 2 < d" by argo
      from c_less d_gr 
      show "c < f r + min \<bar>f r - c\<bar> \<bar>f r - d\<bar> / 2 \<and> f r + min \<bar>f r - c\<bar> \<bar>f r - d\<bar> / 2 < d" by argo
    qed
    moreover have "(f r - (min \<bar>f r - c\<bar> \<bar>f r - d\<bar>)/ 2) \<in> ?cd" 
    proof(rule)
      have "\<bar>f r - c\<bar> / 2 > 0" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by auto
      moreover have "f r > c" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by simp
      ultimately have c_less:"c < f r + \<bar>f r - c\<bar> / 2" by argo
      have "f r < d" using \<open>f r \<in> {x. c < x \<and> x < d}\<close> by simp
      then have d_gr:"f r + \<bar>f r - d\<bar> / 2 < d" by argo
      from c_less d_gr 
      show "c < f r - min \<bar>f r - c\<bar> \<bar>f r - d\<bar> / 2 \<and> f r - min \<bar>f r - c\<bar> \<bar>f r - d\<bar> / 2 < d" by argo
    qed
    ultimately have smalleps_cd:"(f r + ?smalleps) \<in> ?cd" "(f r - ?smalleps) \<in> ?cd" by blast+
    have "?smalleps > 0" using zero_less_abs_iff `f r \<in> ?cd` by auto
    from `\<not>((f r + eps) \<in> ?cd \<and> (f r - eps) \<in> ?cd)` this have "?smalleps < eps"
      using smalleps_cd `?smalleps > 0` eps_def  `f r \<in> ?cd` by auto
    from `?smalleps > 0` assms `r \<in> ?ab` `f r \<in> ?cd` `(f r + ?smalleps) \<in> ?cd` `(f r - ?smalleps) \<in> ?cd`
    have "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < ?smalleps"
      by (rule_tac small_epsilon_inf)
    then obtain del where "del>0" and del_def:"\<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < ?smalleps"
      by blast
    have "\<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps"
    proof (safe)
      fix x
      assume "x \<noteq> r" "\<bar>x - r\<bar> < del"
      from this del_def have "\<bar>f x - f r\<bar> < ?smalleps"
        by blast
      from this `?smalleps < eps` show "\<bar>f x - f r\<bar> < eps" by linarith
    qed
    from this `del>0` show "\<exists>del>0. \<forall>x. x \<noteq> r \<and> \<bar>x - r\<bar> < del \<longrightarrow> \<bar>f x - f r\<bar> < eps" 
      by blast
  qed
qed

lemma bij_betw_shift:assumes bijz:"bij_betw x A (UNIV::real set)" and zy:"(\<lambda>z. y z) = (\<lambda>z. x z + a)" 
  shows "bij_betw y A (UNIV::real set)" 
proof (subst bij_betw_def, rule conjI)
  show "inj_on y A"
  proof (subst inj_on_def, safe)
    fix z1 z2
    assume "z1 \<in> A" "z2 \<in> A" "y z1 = y z2"
    then have "x z1 = x z2" using zy by auto
    from this bijz `z1 \<in> A` `z2 \<in> A`show "z1 = z2"
      by (subst (asm) bij_betw_def, subst (asm) inj_on_def, auto)
  qed
  show "y ` A = UNIV"
  proof (subst image_def, safe)
    fix z assume "z \<in> A"
    have "y z = x z + a" using zy by auto
    from this bijz `z \<in> A`show "y z \<in> UNIV"
      by (subst (asm) bij_betw_def, subst (asm) image_def, auto)
  next
    fix r assume "r \<in> (UNIV::real set)"
    have "\<exists>z \<in> A. x z = (r - a)" 
    proof -
      have "{y. \<exists>z\<in>A. y = x z} = UNIV"  using bijz bij_betw_imp_surj_on image_def
        by fast
      moreover have "(r - a) \<in> UNIV" using iso_tuple_UNIV_I by blast
      ultimately have "(r - a) \<in>{y. \<exists>z\<in>A. y = x z}" by blast
      then show ?thesis by auto
    qed
    then show "\<exists>z\<in>A. r = y z" using zy 
      by force
  qed
qed
end