theory Angles_Brossard_Geometry imports Complex_Main All_True_or_All_False Mod4 Bijection_on_Mono_on
Lines_Brossard_Geometry
begin


locale Bundles = Line_Measure isHalfLine
  for isHalfLine ::"'p set \<Rightarrow> bool" +
  fixes isBundle  :: "('p set) set \<Rightarrow> bool" 
  assumes
  brossard_bundle1: 
"\<lbrakk>g\<noteq>h;\<not>(\<exists> l \<in> Line. g \<union> h = l);g \<in> HalfLine;h \<in> HalfLine;endpoint g = endpoint h\<rbrakk>
\<Longrightarrow> \<exists>!B. isBundle B \<and> g\<in>B \<and> h\<in>B"
and  brossard_bundle2: "\<lbrakk>isBundle B ; g\<in>B ; h\<in>B\<rbrakk> \<Longrightarrow> endpoint g = endpoint h
 \<and> g \<in> HalfLine \<and> h \<in> HalfLine"
context Bundles
begin

definition "Bundle = {x. isBundle x}"

lemma brossard_bundle1': assumes "g\<noteq>h" "\<not>(\<exists> l \<in> Line. g \<union> h = l)" "g \<in> HalfLine" "h \<in> HalfLine"
 "endpoint g = endpoint h"
        shows "\<exists>!B \<in> Bundle. g\<in>B \<and> h\<in>B"
proof -
  from assms have "\<exists>!B. isBundle B \<and> g\<in>B \<and> h\<in>B" by (rule brossard_bundle1)
  then show "\<exists>!B \<in> Bundle. g\<in>B \<and> h\<in>B" using Bundle_def by auto
qed

lemma brossard_bundle2a: assumes "B \<in> Bundle" "g\<in>B" "h\<in>B" 
shows "endpoint g = endpoint h"
proof -
  from assms(1) have "isBundle B" using Bundle_def by auto
  from this assms(2,3) show "endpoint g = endpoint h"
    using brossard_bundle2 by (blast)
qed
  
lemma brossard_bundle2b: assumes "B \<in> Bundle" "g\<in>B" 
                           shows  "g \<in> HalfLine"
proof -
  from assms(1) have "isBundle B" using Bundle_def by auto
  from this assms(2) show "g \<in> HalfLine" 
    using brossard_bundle2 by (blast)
qed

lemma halfline_collinearity: assumes "g\<in>HalfLine" "h \<in> HalfLine" "endpoint g = endpoint h"
  shows"(\<not>(\<exists>l \<in> Line. g \<subseteq> l \<and> h \<subseteq> l)) =  (\<not>(\<exists> l \<in> Line. g \<union> h = l)\<and> g\<noteq>h)"
proof -
  from `g\<in>HalfLine` halfline_distinct_def obtain A X where g_def: "g = halfline X A" "A \<noteq> X"
    by blast
  from this have "X \<in> g" "A \<in> g" using halfline_bestdef by auto
  from `h\<in>HalfLine` halfline_distinct_def obtain B Y where h_def: "h = halfline Y B" "B \<noteq> Y"
    by blast
  from `endpoint g = endpoint h` endpoint_agrees g_def h_def  have h_def: "h = halfline X B" 
"B \<noteq> X"
    by auto
  from this have "X \<in> h" "B \<in> h" using halfline_bestdef by auto
  show ?thesis
  proof  
    assume "\<not> (\<exists>l\<in>Line. g \<subseteq> l \<and> h \<subseteq> l)"
    then have "\<not>(\<exists> l \<in> Line. g \<union> h = l)"
      using sup_ge2 by fastforce
    moreover have "g\<noteq>h" 
    proof (rule ccontr, drule notnotD)
      assume "g = h"
      have "halfline X A \<subseteq> line X A" using halfline_propersubset by blast
      then have "g \<subseteq> line X A" by (subst g_def)
      moreover then have "h \<subseteq> line X A" by (subst(asm) `g = h`)
      ultimately have "\<exists>l\<in>Line. g \<subseteq> l \<and> h \<subseteq> l" using line_bestdef by meson
      from this `\<not> (\<exists>l\<in>Line. g \<subseteq> l \<and> h \<subseteq> l)` show False by contradiction
    qed
    ultimately show "(\<not>(\<exists> l \<in> Line. g \<union> h = l)\<and> g\<noteq>h)" by simp
  next
    assume "\<not>(\<exists> l \<in> Line. g \<union> h = l)\<and> g\<noteq>h"
    then have "\<not>(\<exists> l \<in> Line. g \<union> h = l)" "g\<noteq>h" by auto
    show "\<not>(\<exists>l \<in> Line. g \<subseteq> l \<and> h \<subseteq> l)" 
    proof (rule ccontr, drule notnotD)
      assume "\<exists>l\<in>Line. g \<subseteq> l \<and> h \<subseteq> l"
      then obtain l where "l\<in>Line" "g \<subseteq> l" "h \<subseteq> l" by blast
      from `B \<in> h` `l\<in>Line` `g \<subseteq> l` `h \<subseteq> l` `X \<in> g` `A \<in> g` have "collinear A X B" 
            using collinear_bestdef2 by blast+
      from `B \<in> h` `A \<in> g` `g\<noteq>h` g_def h_def have "A \<noteq> B" by auto
      from `A \<noteq> B` `collinear A X B` `A \<noteq> X` `B \<noteq> X` 
      have "between A B X \<or> between A X B \<or> between B A X"
            by (rule_tac collinear_choice_of_between)
      moreover have "between B A X \<Longrightarrow> g = h" 
        using g_def h_def between_sym between_imp_eq_halflines by auto
      moreover have "between A B X \<Longrightarrow> h = g"
        using g_def h_def between_sym between_imp_eq_halflines by auto
      moreover have "between A X B \<Longrightarrow> line A B = halfline X A \<union> halfline X B" 
        by (rule line_built_from_halflines)
      ultimately have "(\<exists> l \<in> Line. g \<union> h = l) \<or> g=h" using line_bestdef(1) g_def h_def by metis
      from this `\<not>(\<exists> l \<in> Line. g \<union> h = l)\<and> g\<noteq>h` show False by blast
    qed
  qed
qed


lemma noncollinear_endpoint_halfline: 
  assumes"g \<in> HalfLine" shows "\<exists>h \<in> HalfLine. \<not>(\<exists> l \<in> Line. g \<union> h = l)
 \<and> endpoint g = endpoint h \<and> g\<noteq>h"
proof -
  from `g \<in> HalfLine` obtain X A where g_def:"g = halfline X A" and "X \<noteq>A"
    using halfline_distinct_def by blast
  have "(halfline X A) \<in> HalfLine"
    by (rule halfline_bestdef)
  have "endpoint (halfline X A) = X" by (rule endpoint_agrees)
  from point_not_on_line line_bestdef obtain B where "B \<notin> line X A" by presburger
  have halfline:"(halfline X B) \<in> HalfLine"
    by (rule halfline_bestdef)
  have endpoint: "endpoint g = endpoint (halfline X B)" 
    by (subst g_def,(subst  endpoint_agrees)+, rule refl) 
  from halfline_bestdef `X \<noteq>A` point_line_brossard_line2'
  have at_most_one:
"\<forall>l m. l \<in> Line \<and> halfline X A  \<subseteq>  l \<and> m \<in> Line \<and> halfline X A  \<subseteq>  m \<longrightarrow> l = m"
    by blast
  from halfline_propersubset have "halfline X A  \<subseteq>  line X A" by blast 
  have "\<not> ((halfline X B) \<subseteq> (line X A))" using `B \<notin> line X A` halfline_bestdef by blast
  from `B \<notin> line X A` halfline_bestdef line_bestdef line_bestdef
  `halfline X A  \<subseteq>  line X A` g_def at_most_one
  have "\<not>(\<exists> l \<in> Line. g \<union> (halfline X B) = l)"
    by fastforce
  from `B \<notin> line X A` halfline_bestdef
  `halfline X A  \<subseteq>  line X A` g_def
  have "g \<noteq> (halfline X B)"
    by fastforce
  from this `\<not>(\<exists> l \<in> Line. g \<union> (halfline X B) = l)` halfline endpoint show ?thesis by blast
qed
  
lemma brossard_bundle1_single: assumes "g \<in> HalfLine"
        shows "\<exists>B \<in> Bundle. g\<in>B"
  using assms noncollinear_endpoint_halfline brossard_bundle1'
  by metis

end

locale Angle_Measure = Bundles Coord
  for Coord :: "'p set \<Rightarrow> ('p \<Rightarrow> real) set"  +
  fixes Acoord  :: "('p set) set \<Rightarrow> ('p set \<Rightarrow> real) set" 
  assumes
  brossard_angle_measure1: "B \<in> Bundle \<Longrightarrow> \<exists> \<phi>. \<phi> \<in> Acoord B" 
  and brossard_angle_measure2: "\<lbrakk>B \<in> Bundle; \<phi> \<in> Acoord B\<rbrakk> \<Longrightarrow> bij_betw \<phi> B {x. 0\<le>x \<and> x<4}"
  and brossard_angle_measure3: "B \<in> Bundle \<Longrightarrow> \<lbrakk>\<phi>_i \<in> Acoord B ; bij_betw \<phi>_j B {x. 0\<le>x \<and> x<4}\<rbrakk> 
 \<Longrightarrow> ((\<phi>_j \<in> Acoord B) \<equiv>  \<forall> g \<in> B. \<forall> h \<in> B. \<bar>\<phi>_i g - \<phi>_i h\<bar> =4 \<bar>\<phi>_j g - \<phi>_j h\<bar> )"
context Angle_Measure
begin

lemma brossard_angle_measure_2_3: assumes "B \<in> Bundle"
"\<phi>_i \<in> Acoord B" " \<phi>_j \<in> Acoord B" "g \<in> B" "h \<in> B"
                 shows "\<bar>\<phi>_i g - \<phi>_i h\<bar> =4 \<bar>\<phi>_j g - \<phi>_j h\<bar>"
proof -
  from assms(1,3) have "bij_betw \<phi>_j B {x. 0\<le>x \<and> x<4}" by (rule brossard_angle_measure2)
  from assms(1,2) this have 
"((\<phi>_j \<in> Acoord B) \<equiv>  \<forall> g \<in> B. \<forall> h \<in> B. \<bar>\<phi>_i g - \<phi>_i h\<bar> =4 \<bar>\<phi>_j g - \<phi>_j h\<bar>)" 
    by (rule brossard_angle_measure3) 
  from assms(3,4,5) this show ?thesis by fast
qed

lemma halfline_with_measure_r: assumes "B \<in> Bundle" 
"\<phi> \<in> Acoord B" "0 \<le> r \<and> r < 4" shows "\<exists>!g \<in> B. \<phi> g = r"
proof -
  from assms(1,2) have "bij_betw \<phi> B {x. 0 \<le> x \<and> x < 4}" by (rule brossard_angle_measure2)
  then have "\<phi> ` B = {x. 0 \<le> x \<and> x < 4}" by (rule bij_betw_imp_surj_on)
  then have "\<exists>g \<in> B. \<phi> g = r" using assms(3) 
    by (metis (no_types, lifting) imageE mem_Collect_eq)
  from `bij_betw \<phi> B {x. 0 \<le> x \<and> x < 4}` have "inj_on \<phi> B"  by (rule bij_betw_imp_inj_on)
  from this `\<exists>g \<in> B. \<phi> g = r` inj_on_def show ?thesis by metis
qed 

lemma nonhalfline_with_measure_r: assumes 
"bij_betw \<phi> B {x. 0\<le>x \<and> x<4}" "0 \<le> r \<and> r < 4" shows "\<exists>!g \<in> B. \<phi> g = r"
proof -
  from assms(1) have "\<phi> ` B = {x. 0 \<le> x \<and> x < 4}" by (rule bij_betw_imp_surj_on)
  then have "\<exists>g \<in> B. \<phi> g = r" using assms(2) 
    by (metis (no_types, lifting) imageE mem_Collect_eq)
  from `bij_betw \<phi> B {x. 0 \<le> x \<and> x < 4}` have "inj_on \<phi> B"  by (rule bij_betw_imp_inj_on)
  from this `\<exists>g \<in> B. \<phi> g = r` inj_on_def show ?thesis by metis
qed

lemma acoordfn_preserves_distinctness_eq: 
      assumes "B \<in> Bundle" and  "\<phi>\<in> Acoord B" and "h \<in> B" and "g \<in> B"
      shows "(g=h) = (\<phi> g = \<phi> h)"
proof (rule iffI,erule arg_cong, rule ccontr)
  assume "\<phi> g = \<phi> h"
  assume "g \<noteq> h"
  from assms(1,2) have "bij_betw \<phi> B {x. 0\<le>x \<and> x<4}" by (rule brossard_angle_measure2)
  then have "inj_on \<phi> B" using bij_betw_def by blast
  then have "(\<forall>z\<in>B. \<forall>y\<in>B. \<phi> z = \<phi> y \<longrightarrow> z = y)" by (subst inj_on_def[symmetric])
  from this `\<phi> g = \<phi> h` assms(3,4) have "g=h" by fast
  from this `g \<noteq> h` show False by safe
qed

lemma acoordfn_bounds: assumes "B \<in> Bundle" and  "\<phi>\<in> Acoord B" and "h \<in> B" 
       shows "0 \<le> \<phi> h \<and> \<phi> h < 4"
proof -
  from assms(1,2)have "bij_betw \<phi> B {x. 0\<le>x \<and> x<4}" by (rule brossard_angle_measure2)
  then have "\<phi> ` B = {x. 0\<le>x \<and> x<4}" by (subst(asm) bij_betw_def, rule_tac conjunct2) 
  from `h \<in> B` this show "0 \<le> \<phi> h \<and> \<phi> h < 4" using image_def by blast
qed

lemma acoordfn_preserves_distinctness_eq4: 
      assumes "B \<in> Bundle" and  "\<phi>\<in> Acoord B" and "h \<in> B" and "g \<in> B"
      shows "(g=h) = (\<phi> g =4 \<phi> h)"
proof (rule iffI)
  assume "g=h"
  show "\<phi> g =4 \<phi> h" by (subst `g=h`, rule eq4_refl)
next
  assume "\<phi> g =4 \<phi> h"
  from assms(1,2) `g \<in> B` have "0 \<le> \<phi> g \<and> \<phi> g < 4" by (rule acoordfn_bounds)
  from assms(1,2) `h \<in> B` have "0 \<le> \<phi> h \<and> \<phi> h < 4" by (rule acoordfn_bounds)
  from `\<phi> g =4 \<phi> h` `0 \<le> \<phi> g \<and> \<phi> g < 4` `0 \<le> \<phi> h \<and> \<phi> h < 4` have "\<phi> g = \<phi> h" by (rule eq4_imp_eq)
  from this assms show "g=h" by (subst(asm) acoordfn_preserves_distinctness_eq[symmetric])
qed

definition 
"\<lbrakk>g \<in> HalfLine;h \<in> HalfLine;endpoint g = endpoint h; \<phi> \<in> Acoord B; g \<in>B; h \<in>B; B \<in> Bundle\<rbrakk>
          \<Longrightarrow> ((ameasure_rel \<phi> g h)::real) = min (mod4 (\<phi> g - \<phi> h)) (mod4 (\<phi> h - \<phi> g))"

lemma ameasure_rel_commutes:
"\<lbrakk>g \<in> HalfLine;h \<in> HalfLine;endpoint g = endpoint h; \<phi> \<in> Acoord B; g \<in>B; h \<in>B; B \<in> Bundle\<rbrakk>
                           \<Longrightarrow> ((ameasure_rel \<phi> g h)::real) = ((ameasure_rel \<phi> h g)::real)"
  using ameasure_rel_def by simp

lemma ameasure_rel_bounds: 
  assumes "g \<in> HalfLine" "h \<in> HalfLine" "endpoint g = endpoint h" 
"\<phi> \<in> Acoord B" "g \<in>B" "h \<in>B" "B \<in> Bundle"
  shows
"0 \<le> ameasure_rel \<phi> g h \<and> ameasure_rel \<phi> g h \<le> 2"
proof -
  have "0 \<le> min (mod4 (\<phi> g - \<phi> h)) (mod4 (\<phi> h - \<phi> g)) 
\<and> min (mod4 (\<phi> g - \<phi> h)) (mod4 (\<phi> h - \<phi> g)) \<le> 2"
    by (rule min_mod4_difference_bounds)
  from this assms show ?thesis using ameasure_rel_def by auto
qed

lemma coinciding_HalfLines: assumes
"\<phi> \<in> Acoord B_X" 
"g \<in> B_X" "h \<in> B_X" "B_X \<in> Bundle"
      shows "(g = h) = (ameasure_rel \<phi> g h = 0)"
proof -
  from assms(2,3,4) have "endpoint g = endpoint h" by (rule_tac brossard_bundle2a)
  from assms(2,4)have "g \<in> HalfLine" by (rule_tac brossard_bundle2b)
  from assms(3,4)have "h \<in> HalfLine" by (rule_tac brossard_bundle2b)
  from `g \<in> HalfLine` obtain X A where g_def:"g = halfline X A" 
    using halfline_distinct_def by blast
  from `h \<in> HalfLine` obtain Y B where h_def:"h = halfline Y B" 
    using halfline_distinct_def by blast
  from g_def h_def `endpoint g = endpoint h` have h_def:"h = halfline X B" 
    using endpoint_agrees by simp
  have "(halfline X A) \<in> HalfLine" and "(halfline X B) \<in> HalfLine" 
    by (rule_tac [!] halfline_bestdef)
  moreover have "endpoint (halfline X A) = X" and "endpoint (halfline X B) = X"
    by (rule_tac [!] endpoint_agrees)
  ultimately have angle_AXB:"ameasure_rel \<phi> (halfline X A) (halfline X B) 
  = min (mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))) (mod4 (\<phi> (halfline X B) - \<phi> (halfline X A)))"
    using assms ameasure_rel_def g_def h_def endpoint_agrees by auto
  show ?thesis
  proof
    assume "g = h"
    have "\<phi> (halfline X A) = \<phi> (halfline X B)"
      by (subst g_def[symmetric], subst h_def[symmetric], subst `g = h`, rule refl)
    then have sym:"mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))
 = mod4 (\<phi> (halfline X B) - \<phi> (halfline X A))"
      by simp
    have "\<phi> (halfline X A) - \<phi> (halfline X B) =4 mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))"
      by (rule mod4_bestdef)
    from `\<phi> (halfline X A) = \<phi> (halfline X B)` this 
    have "0 =4 mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))" 
      by fastforce
    have bounds: "0\<le> mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))
 \<and> mod4 (\<phi> (halfline X A) - \<phi> (halfline X B)) < 4"
      using mod4_bestdef by blast
    have "0 \<le> (0::real) \<and> (0::real) < 4" by simp
    from `0 =4 mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))` this bounds
    have "0 = mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))" by (rule eq4_imp_eq) 
    from this sym have 
    "(min(mod4(\<phi> (halfline X A) - \<phi> (halfline X B))) 
(mod4 (\<phi> (halfline X B) - \<phi> (halfline X A))))=0"
      by auto
    from this show "ameasure_rel \<phi> g h = 0" 
      by (subst g_def, subst h_def, subst(asm) angle_AXB[symmetric])
  next
    assume "ameasure_rel \<phi> g h = 0"
    then have "ameasure_rel \<phi> (halfline X A) (halfline X B) = 0"
      by (subst g_def[symmetric], subst h_def[symmetric])
    show "g = h" 
    proof -
      from `ameasure_rel \<phi> (halfline X A) (halfline X B) = 0` 
      have "(min(mod4(\<phi> (halfline X A) - \<phi> (halfline X B))) 
(mod4 (\<phi> (halfline X B) - \<phi> (halfline X A))))=0"
        by (subst(asm) angle_AXB)
      then consider "mod4(\<phi> (halfline X A) - \<phi> (halfline X B)) = 0"|
                    "mod4(\<phi> (halfline X B) - \<phi> (halfline X A)) = 0"
        by linarith
      then have "mod4(\<phi> (halfline X A) - \<phi> (halfline X B)) = 0"
      proof (cases, assumption)
        assume "mod4(\<phi> (halfline X B) - \<phi> (halfline X A)) = 0"
        then have "mod4(-(\<phi> (halfline X B) - \<phi> (halfline X A))) = 0" by (rule mod4_zero)
        then show "mod4(\<phi> (halfline X A) - \<phi> (halfline X B)) = 0" by simp
      qed
      have "0 =4 \<phi> (halfline X A) - \<phi> (halfline X B)" 
        by (rule eqmod4_imp_eq4, subst `mod4(\<phi> (halfline X A) - \<phi> (halfline X B)) = 0`, rule refl)
      then have "\<phi> (halfline X A) =4 0 - (-\<phi> (halfline X B))" 
      proof -
        have "\<phi> (halfline X B) =4 \<phi> (halfline X A)"
          using \<open>0 =4 \<phi> (halfline X A) - \<phi> (halfline X B)\<close> eq4_swap by force
        then have "\<phi> (halfline X A) =4 \<phi> (halfline X B)"
          by (meson eq4_sym)
        then show ?thesis
          by simp
      qed
      then have "\<phi> (halfline X A) =4 \<phi> (halfline X B)" by simp
      from `B_X \<in> Bundle`  `\<phi> \<in> Acoord B_X` `g \<in> B_X` 
      have "0 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 4" 
        by (subst g_def[symmetric], subst g_def[symmetric], rule acoordfn_bounds)
      from `B_X \<in> Bundle`  `\<phi> \<in> Acoord B_X` `h \<in> B_X`
      have "0 \<le> \<phi> (halfline X B) \<and> \<phi> (halfline X B) < 4"
        by (subst h_def[symmetric], subst h_def[symmetric], rule acoordfn_bounds)
      from `\<phi> (halfline X A) =4 \<phi> (halfline X B)` `0 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 4`
      `0 \<le> \<phi> (halfline X B) \<and> \<phi> (halfline X B) < 4` have "\<phi> (halfline X A) = \<phi> (halfline X B)" 
        by (rule eq4_imp_eq)
      from `B_X \<in> Bundle`  `\<phi> \<in> Acoord B_X` `g \<in> B_X` `h \<in> B_X` this show "g = h" 
        by (subst(asm) g_def[symmetric], subst(asm) h_def[symmetric],
                            subst acoordfn_preserves_distinctness_eq)
    qed
  qed
qed

lemma coinciding_halflines: assumes
"\<phi> \<in> Acoord B_X"
"halfline X A \<in> B_X" "halfline X B \<in> B_X"  "B_X \<in> Bundle"
      shows "(halfline X A = halfline X B) = (ameasure_rel \<phi> (halfline X A) (halfline X B) = 0)"
  by (rule coinciding_HalfLines, rule_tac [!] assms)

lemma weak_coinciding_halflines: assumes
"\<phi> \<in> Acoord B_X"
"halfline X A \<in> B_X" "halfline X B \<in> B_X"  "B_X \<in> Bundle"
shows "(halfline X A = halfline X B) = (ameasure_rel \<phi> (halfline X A) (halfline X B) =4 0)"
proof -
  have "0\<le>(0::real) \<and> (0::real) <4" 
    by simp
  from assms
  have "(halfline X A = halfline X B) = (ameasure_rel \<phi> (halfline X A) (halfline X B) = 0)"
    by (rule coinciding_halflines)
  from this have "(halfline X A = halfline X B) 
= (min (mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))) 
(mod4 (\<phi> (halfline X B) - \<phi> (halfline X A))) = 0)"
    using ameasure_rel_def halfline_bestdef assms endpoint_agrees by presburger
  also from `0\<le>(0::real) \<and> (0::real) <4` have "... = 
(min (mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))) 
(mod4 (\<phi> (halfline X B) - \<phi> (halfline X A))) =4 0)"
    by (rule min_mod4_eq4_eq[symmetric])
  finally show ?thesis using ameasure_rel_def halfline_bestdef assms endpoint_agrees by presburger
qed

lemma measure_independence: assumes "B_X \<in> Bundle" "(halfline X A) \<in>B_X" "(halfline X B) \<in>B_X"
       shows "\<exists>ameasure. \<forall>\<phi>\<in>Acoord B_X. ameasure = ameasure_rel \<phi> (halfline X A) (halfline X B)"
proof -
  from assms(1) obtain \<phi> where "\<phi> \<in> Acoord B_X" by (rule_tac exE, rule brossard_angle_measure1)
  have "\<forall>\<psi>\<in>Acoord B_X. ameasure_rel \<phi> (halfline X A) (halfline X B) 
= ameasure_rel \<psi> (halfline X A) (halfline X B)"
  proof
    fix \<psi>
    assume "\<psi>\<in>Acoord B_X"
    have halflineXAXB: "halfline X A \<in> HalfLine" "halfline X B \<in> HalfLine"
      by (rule_tac [!] halfline_bestdef)
    have endpointX: "endpoint (halfline X A) = X" "endpoint (halfline X B) = X" 
      by (rule_tac [!] endpoint_agrees)
    from halflineXAXB endpointX `\<phi> \<in> Acoord B_X` assms(2,3,1)
    have phi_ameasure:"ameasure_rel \<phi> (halfline X A) (halfline X B) 
    = min (mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))) 
(mod4 (\<phi> (halfline X B) - \<phi>(halfline X A)))"
      using ameasure_rel_def by force
    from `B_X \<in> Bundle` `\<phi> \<in> Acoord B_X` `\<psi> \<in> Acoord B_X`
    `(halfline X A) \<in> B_X` `(halfline X B) \<in> B_X`
    have "\<bar>\<phi> (halfline X A) - \<phi> (halfline X B)\<bar> =4 \<bar>\<psi> (halfline X A) - \<psi> (halfline X B)\<bar>" 
      by (rule brossard_angle_measure_2_3)
    then have psi_phi_eq:
    "min (mod4 (\<phi> (halfline X A) - \<phi> (halfline X B))) 
(mod4 (-(\<phi> (halfline X A) - \<phi> (halfline X B))))
    = min (mod4 (\<psi> (halfline X A) - \<psi> (halfline X B))) 
(mod4 (-(\<psi> (halfline X A) - \<psi> (halfline X B))))"
      by (rule eq4_abs)
    from halflineXAXB endpointX `\<psi> \<in> Acoord B_X` assms(2,3,1)
    have psi_ameasure: "ameasure_rel \<psi> (halfline X A) (halfline X B) 
    = min (mod4 (\<psi> (halfline X A) - \<psi> (halfline X B)))
 (mod4 (\<psi> (halfline X B) - \<psi>(halfline X A)))"
      using ameasure_rel_def by force
    from psi_phi_eq psi_ameasure phi_ameasure
    show "ameasure_rel \<phi> (halfline X A) (halfline X B)
 = ameasure_rel \<psi> (halfline X A) (halfline X B)"
      by simp
  qed
  then show ?thesis by blast
qed

lemma HalfLine_measure_independence: assumes "B \<in> Bundle" "g \<in>B" "h \<in>B" 
"endpoint g = endpoint h" "\<phi>\<in>Acoord B" "\<psi>\<in>Acoord B"
shows "ameasure_rel \<phi> g h = ameasure_rel \<psi> g h"
proof -
  define X where "X = endpoint g"
  from assms (1,2,3) have "X = endpoint h" by (subst X_def, rule brossard_bundle2a)
  from assms(1,2) have "g \<in> HalfLine" by (rule brossard_bundle2b) 
  from this halfline_distinct_def endpoint_agrees X_def obtain A where
  g_def:"g = halfline X A" and "A \<noteq> X"
    by force
  from `g \<in>B` have "halfline X A \<in> B" by (subst(asm) `g = halfline X A`)
  from assms(1,3) have "h \<in> HalfLine" by (rule brossard_bundle2b) 
  from this halfline_distinct_def endpoint_agrees `X = endpoint h` obtain P where
  h_def:"h = halfline X P" and "P \<noteq> X"
    by force 
  from `h \<in>B` have "halfline X P \<in> B" by (subst(asm) `h = halfline X P`)
  from `B \<in> Bundle` `halfline X A \<in> B` `\<phi>\<in> Acoord B` `\<psi>\<in> Acoord B` `halfline X P \<in> B`
  have "(ameasure_rel \<phi> (halfline X A) (halfline X P))
 = (ameasure_rel \<psi> (halfline X A) (halfline X P))"
    using measure_independence
    by metis
  then show ?thesis by ((subst g_def)+,(subst h_def)+)
qed

definition "bundle g h = (SOME B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B)"

lemma unique_candidate: assumes "\<exists>!B. P B" 
  shows"(THE B. P B) = (SOME B. P B)"
  by (metis assms some_equality the_equality)

lemma bundle_old_def: assumes "g \<in> HalfLine" "h \<in> HalfLine" "endpoint g = endpoint h"
  shows
"bundle g h = (if  (\<not> (\<exists>l\<in>Line. g \<union> h = l) \<and> g \<noteq> h) then THE B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B
                          else SOME B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B)"
proof (cases "(\<not> (\<exists>l\<in>Line. g \<union> h = l) \<and> g \<noteq> h)")
  assume asm: "(\<not> (\<exists>l\<in>Line. g \<union> h = l) \<and> g \<noteq> h)"
  from assms this have "\<exists>!B. B \<in> Bundle \<and> g \<in> B \<and> h \<in> B" using brossard_bundle1' by auto
  then have one_bundle:"(THE B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B) = (SOME B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B)"
    by (rule unique_candidate)
  show ?thesis using bundle_def
    by (simp add: one_bundle)
next
  assume "\<not> (\<not> (\<exists>l\<in>Line. g \<union> h = l) \<and> g \<noteq> h)"
  then show ?thesis using bundle_def by presburger
qed 
  

definition 
"ameasure == (SOME ameasure. \<forall>g h. \<forall>\<phi> \<in> Acoord (bundle g h). ameasure g h = ameasure_rel \<phi> g h)" 
(*we need to consider the bundle defined by g h to show ameasure is bundle-independent!*)
(*do we? could just define it relative to bundle, then show independence.*)

lemma between_bestdef:"\<forall>g\<in>HalfLine.\<forall>h\<in>HalfLine. \<forall>\<phi> \<in> Acoord (bundle g h).
 endpoint g = endpoint h \<longrightarrow> ameasure g h = ameasure_rel \<phi> g h" 
oops
    
end

locale Continuity = Angle_Measure  isLine
  for isLine ::"'p set \<Rightarrow> bool" +
  assumes brossard_continuity: 
  "\<lbrakk>B_X \<in> Bundle;g \<in> B_X;h \<in> B_X;A\<noteq>(endpoint g);B\<noteq>(endpoint g);A\<noteq>B;A\<in>g;B\<in>h;
   \<phi> \<in> (Acoord B_X);\<not>(\<exists> l \<in> Line. g \<union> h = l); between A P B \<or> P=A\<or>P=B\<rbrakk>
    \<Longrightarrow> \<exists>C. (halfline (endpoint g) C)\<in>B_X \<and> P \<in> (halfline (endpoint g) C) 
     \<and> ameasure_rel \<phi> (halfline (endpoint g) A) (halfline (endpoint g) P) +
     ameasure_rel \<phi> (halfline (endpoint g) P) (halfline (endpoint g) B) =4
     ameasure_rel \<phi> (halfline (endpoint g) A) (halfline (endpoint g) B)"
(*Does need =4 because the minimum of the two guys added together isn't necessarily the minimum of 
each added.*)
context Continuity
begin

lemma brossard_continuity_halfline: assumes "B_X \<in> Bundle" "\<phi> \<in> Acoord B_X"
  "between A P B \<or> P=A\<or>P=B"
 "halfline X A \<in> B_X" "halfline X B \<in> B_X"  "A \<noteq> X" "B \<noteq> X" "A \<noteq> B" 
 "\<not>(\<exists>l\<in>Line. (halfline X A) \<union> (halfline X B) = l)"
shows "\<exists>C. (halfline X C)\<in>B_X \<and> P \<in> (halfline X C) 
     \<and> ameasure_rel \<phi> (halfline X A) (halfline X P) +
     ameasure_rel \<phi> (halfline X P) (halfline X B) =4
     ameasure_rel \<phi> (halfline X A) (halfline X B)"
proof-
  define g where "g = halfline X A"
  from `halfline X A \<in> B_X` have "g \<in> B_X" by (subst g_def)
  define h where "h = halfline X B"
  from `halfline X B \<in> B_X` have "h \<in> B_X" by (subst h_def)
  from g_def have "endpoint g  = X" using endpoint_agrees by simp
  have "A \<in> halfline X A" "X \<in> halfline X A"  by (rule_tac [!] halfline_bestdef)
  from this g_def have "A \<in> g" "X \<in> g" by auto
  have "B \<in> halfline X B" by (rule halfline_bestdef)
  from this h_def have "B \<in> h" by simp
  have "\<not> (\<exists>l\<in>Line. g \<union> h = l)" using `\<not>(\<exists>l\<in>Line. (halfline X A) \<union> (halfline X B) = l)`
 g_def h_def by simp
  have "A \<noteq> endpoint g" "B \<noteq> endpoint g" using `endpoint g  = X` `A \<noteq> X` `B \<noteq> X` by auto
  have "\<exists>C. halfline (endpoint g) C \<in> B_X \<and>
    P \<in> halfline (endpoint g) C \<and>
    ameasure_rel \<phi> (halfline (endpoint g) A) (halfline (endpoint g) P) +
    ameasure_rel \<phi> (halfline (endpoint g) P) (halfline (endpoint g) B) =4
    ameasure_rel \<phi> (halfline (endpoint g) A) (halfline (endpoint g) B)"
    using assms(1,2,3) `g \<in> B_X` `h \<in> B_X` `A \<noteq> endpoint g` `B \<noteq> endpoint g` `endpoint g  = X`
    `\<not> (\<exists>l\<in>Line. g \<union> h = l)` `A \<in> g` `B \<in> h` `A \<noteq> B`
    by (rule_tac h = "h" and g = "g" in brossard_continuity)
  then show ?thesis using `endpoint g  = X`
    by fast
qed


lemma pi_imp_straight: assumes "B_X \<in> Bundle" "g \<in> B_X" "h \<in> B_X" "\<phi> \<in> (Acoord B_X)"
 "ameasure_rel \<phi> g h = 2" 
        shows "\<exists> l \<in> Line. g \<union> h = l"
proof (rule ccontr)
  assume "\<not>(\<exists> l \<in> Line. g \<union> h = l)"
  define X where "X = endpoint g"
  from assms (1,2,3) have "X = endpoint h" by (subst X_def, rule brossard_bundle2a)
  from assms(1,2) have "g \<in> HalfLine" by (rule brossard_bundle2b) 
  from this halfline_distinct_def endpoint_agrees X_def obtain A where
  g_def:"g = halfline X A" and "A \<noteq> X"
    by force
  from assms(1,3) have "h \<in> HalfLine" by (rule brossard_bundle2b) 
  from this halfline_distinct_def endpoint_agrees `X = endpoint h` obtain P where
  h_def:"h = halfline X P" and "P \<noteq> X"
    by force    
  from assms(4,2,3,1) have 
  "(halfline X A = halfline X P) = (ameasure_rel \<phi> (halfline X A) (halfline X P) = 0)"
    by (subst(asm) g_def,subst(asm) h_def,rule_tac coinciding_halflines)
  from this assms(5) have "halfline X A \<noteq> halfline X P"
    by (subst(asm) g_def, subst(asm) h_def, simp)
  then have "A\<noteq>P" by auto
  have "\<exists>B\<in>(line A P). between B P A"
  proof -
    have "line A P \<in> Line" by (rule line_bestdef)
    then obtain x where x_def: "x \<in> Coord (line A P)"
      by (rule_tac exE, rule brossard_line_measure1)
    from `line A P \<in> Line` x_def have "bij_betw x (line A P) (UNIV::real set)"
      by (rule brossard_line_measure2)
    from `bij_betw x (line A P) UNIV` have "x ` (line A P) = (UNIV::real set)" 
      by (subst(asm) bij_betw_def, rule_tac conjunct2)
    from this have im:"{y. \<exists>z\<in>(line A P). y = x z} = UNIV" by (subst(asm) image_def)
    from x_def `A \<noteq> P` have "x A \<noteq> x P" 
      by (subst(asm) coordfn_preserves_distinctness, auto simp: line_bestdef)
    then consider "x A > x P" | "x A < x P" by linarith
    then show ?thesis
    proof (cases)
      assume "x A > x P"
      from im obtain B where "B \<in> (line A P)" and "x P -1 = x B" by blast
      from this `x A > x P` have "x B < x P \<and> x P < x A" by simp
      from this x_def between_expanded_def `B \<in> (line A P)` have "between B P A" 
        by (simp add: between_sym)
      from this `B \<in> (line A P)` show ?thesis by blast
    next
      assume "x P > x A"
      from im obtain B where "B \<in> (line A P)" and "x P + 1 = x B" by blast
      from this `x P > x A` have "x B > x P \<and> x P > x A" by simp
      from this x_def between_expanded_def `B \<in> (line A P)` have "between B P A" 
        by (simp add: between_sym)
      from this `B \<in> (line A P)` show ?thesis by blast
    qed
  qed
  then obtain B where "B \<in> (line A P)" and "between B P A" by (rule bexE)
  then have "A \<noteq> B" using bet_imp_distinct by blast
  from `A \<noteq> X` halfline_def have halflineXA_def: 
"halfline X A = {P. \<not> between A X P \<and> P \<in> line X A}"
    by presburger
  from `P \<noteq> X` halfline_def have halflineXP_def: 
"halfline X P = {Q. \<not> between P X Q \<and> Q \<in> line X P}"
    by presburger
  have "\<not> (B \<in> (line X A))" 
  proof (rule ccontr, drule notnotD)
    assume "B \<in> (line X A)"
    have "A \<in> (line X A)" by (rule line_bestdef)
    from  `A \<noteq> X` have "line X A \<in> Line" by (rule_tac line_bestdef)
    from this `A \<in> (line X A)` `B \<in> (line X A)` `A \<noteq> B` have "line X A = line A B" 
      by (rule_tac line_bestdef_inv)
    have "A \<in> (line A P)" by (rule line_bestdef)      
    from `A \<noteq> P` have "line A P \<in> Line" by (rule_tac line_bestdef)
    from this `B \<in> (line A P)`  `A \<in> (line A P)` `A \<noteq> B` have "line A P = line A B" 
      by (rule_tac line_bestdef_inv)
    from `line X A = line A B` this have "line A P = line X A" by simp
    from `line A P = line X A` line_sym have "P \<in> line A X"
      using \<open>A \<noteq> P\<close> unique_line(3) by auto
    from `P \<in> line A X` have "collinear A X P" using collinear_def by auto
    consider "between A P X \<or> between P A X" | "between A X P"  using `A \<noteq> X` `A \<noteq> P` `P \<noteq> X` 
    `collinear A X P` collinear_choice_of_between by blast
    then show False 
    proof (cases)
      case 1 
      from this between_sym sameside_def have "sameside A P X" by auto
      then have "halfline X A = halfline X P" by (rule sameside_imp_eq_halflines)
      from `halfline X A \<noteq> halfline X P` this show False by contradiction
    next
      case 2
      then have "line A P = halfline X A \<union> halfline X P" by (rule line_built_from_halflines)
      from this `\<not>(\<exists> l \<in> Line. g \<union> h = l)` g_def h_def line_bestdef show False by metis
    qed 
  qed
  from `halfline X A \<noteq> halfline X P` between_imp_eq_halflines
  have "\<not>between X P A" by blast
  from this `between B P A` have "B \<noteq> X" by blast   
  from `g \<in> B_X` have "halfline X A \<in> B_X" by (subst(asm) g_def)
  from `h \<in> B_X` have "halfline X P \<in> B_X" by (subst(asm) h_def)
  have "halfline X A \<in> HalfLine" by (rule halfline_bestdef)
  have "halfline X B \<in> HalfLine" by (rule halfline_bestdef)
  have endpointX:"endpoint (halfline X A) = endpoint (halfline X B)" using endpoint_agrees by auto
  have "\<not> (\<exists>l\<in>Line. halfline X A \<union> halfline X B = l)" 
  proof 
    assume "\<exists>l\<in>Line. halfline X A \<union> halfline X B = l"
    then obtain l where "l\<in>Line" and l_def:"halfline X A \<union> halfline X B = l" by blast+
    have "A \<in> halfline X A" "X \<in> halfline X A" "B \<in> halfline X B" using halfline_bestdef by auto
    from this l_def have "A \<in> l" "X \<in> l" "B \<in>l" by blast+
    from this `A \<noteq> X`[symmetric] `l \<in> Line` have "l = line X A" by (rule_tac line_bestdef_inv)
    from `\<not> (B \<in> (line X A))` this have "\<not> (B \<in> l)" by blast
    from `B \<in>l` this show False by contradiction
  qed
  from `\<not> (B \<in> (line X A))` have "halfline X A \<noteq> halfline X B" 
    using halfline_bestdef halflineXA_def by blast
  from this `\<not> (\<exists>l\<in>Line. halfline X A \<union> halfline X B = l)` `halfline X A \<in> HalfLine` 
  `halfline X B \<in> HalfLine` `endpoint (halfline X A) = endpoint (halfline X B)` 
  have  "\<exists>!Bu. Bu \<in> Bundle \<and> (halfline X A) \<in> Bu \<and> (halfline X B) \<in> Bu"
    by (rule_tac brossard_bundle1')
  then obtain Bu where Bu_def: "Bu \<in> Bundle" "(halfline X A) \<in> Bu" "(halfline X B) \<in> Bu" by blast
  then obtain \<psi> where psi_def:"\<psi> \<in> Acoord Bu" using brossard_angle_measure1 by blast
  from `between B P A` have "between A P B \<or> P = A \<or> P = B" using between_sym by simp
  from psi_def `A \<noteq> X` `P \<noteq> X` `A \<noteq> P` `A \<noteq> B` this
  `B \<noteq> X` Bu_def `\<not> (\<exists>l\<in>Line. halfline X A \<union> halfline X B = l)`
  `\<psi> \<in> Acoord Bu`
  have "\<exists>C. (halfline X C)\<in>Bu \<and> P \<in> (halfline X C) 
     \<and> ameasure_rel \<psi> (halfline X A) (halfline X P) +
     ameasure_rel \<psi> (halfline X P) (halfline X B) =4
     ameasure_rel \<psi> (halfline X A) (halfline X B)"
    by (rule_tac brossard_continuity_halfline)
  then obtain C where C_def:"(halfline X C)\<in>Bu" " P \<in> (halfline X C)" by blast
  from this `P\<noteq>X` have "(halfline X C) = (halfline X P)" by (rule_tac halfline_independence)
  then have "(halfline X P) \<in> Bu" using C_def by simp
  from `halfline X A \<noteq> halfline X P` g_def h_def have "g\<noteq>h" by simp
  from `X = endpoint g` `X = endpoint h` have "endpoint g = endpoint h" by simp
  from`g\<noteq>h` `\<not> (\<exists>l\<in>Line. g \<union> h = l)` `g \<in> HalfLine` `h \<in> HalfLine` `endpoint g = endpoint h`
  have one_bundle:"\<exists>!B. B \<in> Bundle \<and> g \<in> B \<and> h \<in> B" by (rule_tac brossard_bundle1')
  from `(halfline X A) \<in> Bu` `(halfline X P) \<in> Bu` g_def h_def have "g \<in> Bu" "h \<in> Bu"
    by (argo, argo)
  from this `Bu \<in> Bundle` `B_X \<in> Bundle` `g\<in>B_X` `h\<in>B_X` one_bundle have "Bu = B_X"
    by auto
  then have "(halfline X B) \<in> B_X" using `(halfline X B) \<in> Bu` by simp 
  from `\<phi> \<in> (Acoord B_X)` `A \<noteq> X` `P \<noteq> X` `A \<noteq> P` `A \<noteq> B`  `(halfline X A) \<in> B_X`
  `B \<noteq> X` `B_X \<in> Bundle` `\<not> (\<exists>l\<in>Line. halfline X A \<union> halfline X B = l)` `(halfline X B) \<in> B_X`
 `between A P B \<or> P = A \<or> P = B`
  have ABPsum:"\<exists>C. (halfline X C)\<in>B_X \<and> P \<in> (halfline X C) 
     \<and> ameasure_rel \<phi> (halfline X A) (halfline X P) +
     ameasure_rel \<phi> (halfline X P) (halfline X B) =4
     ameasure_rel \<phi> (halfline X A) (halfline X B)" 
    by (rule_tac brossard_continuity_halfline)
  from `ameasure_rel \<phi> g h = 2` have "ameasure_rel \<phi> (halfline X A) (halfline X P) = 2"
    by (subst(asm) g_def, subst(asm) h_def)
  from ABPsum have ABPsum2:"2 + ameasure_rel \<phi> (halfline X P) (halfline X B) =4
        ameasure_rel \<phi> (halfline X A) (halfline X B)"
    by (subst(asm) `ameasure_rel \<phi> (halfline X A) (halfline X P) = 2`, blast)
  from  `B \<notin> line X A` `B \<in> line A P`
  have "B \<notin> line X P" 
    by (metis \<open>A \<noteq> X\<close> \<open>between B P A\<close> bet_imp_distinct(1) on_line_sym same_line)
  then have "halfline X P \<noteq> halfline X B" by (rule halfline_independence_inv)
  from this `\<phi> \<in> Acoord B_X` `halfline X P \<in> B_X` `halfline X B \<in> B_X` `B_X \<in> Bundle`
  have "ameasure_rel \<phi> (halfline X P) (halfline X B) \<noteq> 0"
    by (subst coinciding_halflines[symmetric])
  have "ameasure_rel \<phi> (halfline X P) (halfline X B) \<noteq> 2"
  proof (rule ccontr, drule notnotD)
    assume "ameasure_rel \<phi> (halfline X P) (halfline X B) = 2"
    from ABPsum2 have "2 + 2 =4
        ameasure_rel \<phi> (halfline X A) (halfline X B)"
      by (subst(asm) `ameasure_rel \<phi> (halfline X P) (halfline X B) = 2`)
    then have "ameasure_rel \<phi> (halfline X A) (halfline X B) =4 4" by (simp add: eq4_sym)
    then have "ameasure_rel \<phi> (halfline X A) (halfline X B) =4 0" 
      by (rule eq4_trans, rule_tac eq4_4_0)
    from this `\<phi> \<in> Acoord B_X` `halfline X A \<in> B_X` `halfline X B \<in> B_X` `B_X \<in> Bundle`
    have "(halfline X A) = (halfline X B)" by (subst weak_coinciding_halflines)
    from `\<not> (B \<in> (line X A))` have "(halfline X A) \<noteq> (halfline X B)"
      using halfline_independence_inv by blast
    from this `(halfline X A) = (halfline X B)` show False by contradiction
  qed
  from ABPsum2 have "mod4( 2 + ameasure_rel \<phi> (halfline X P) (halfline X B)) =
       mod4 ( ameasure_rel \<phi> (halfline X A) (halfline X B))" by (subst mod4_eq4)
  then have ABPsum3:"mod4( 2 + ameasure_rel \<phi> (halfline X P) (halfline X B)) =
  ameasure_rel \<phi> (halfline X A) (halfline X B)" using ameasure_rel_def mod4_min_projection_property
  halfline_bestdef assms endpoint_agrees `halfline X A \<in> B_X` `halfline X B \<in> B_X` by presburger
  have "0\<le>ameasure_rel \<phi> (halfline X P) (halfline X B)
 \<and> ameasure_rel \<phi> (halfline X P) (halfline X B)\<le> 2" using  halfline_bestdef assms endpoint_agrees
 `halfline X B \<in> B_X` ameasure_rel_bounds \<open>halfline X P \<in> B_X\<close> by auto
  from this `ameasure_rel \<phi> (halfline X P) (halfline X B) \<noteq> 2`
 `ameasure_rel \<phi> (halfline X P) (halfline X B) \<noteq> 0`
  have "0<ameasure_rel \<phi> (halfline X P) (halfline X B)
 \<and> ameasure_rel \<phi> (halfline X P) (halfline X B)< 2" by linarith
  from this
  have "2< 2 + ameasure_rel \<phi> (halfline X P) (halfline X B)
 \<and>  2 + ameasure_rel \<phi> (halfline X P) (halfline X B)< 4" by linarith
  from this have "2< mod4(2 + ameasure_rel \<phi> (halfline X P) (halfline X B))
 \<and> mod4( 2 + ameasure_rel \<phi> (halfline X P) (halfline X B))< 4" using mod4_simple by auto
  moreover have "0\<le>ameasure_rel \<phi> (halfline X A) (halfline X B)
 \<and> ameasure_rel \<phi> (halfline X A) (halfline X B)\<le> 2" using  halfline_bestdef assms endpoint_agrees
 `halfline X B \<in> B_X` ameasure_rel_bounds \<open>halfline X A \<in> B_X\<close> by auto  
  ultimately have "mod4( 2 + ameasure_rel \<phi> (halfline X P) (halfline X B)) \<noteq>
  ameasure_rel \<phi> (halfline X A) (halfline X B)" by argo
  from this ABPsum3 show False by contradiction
qed

lemma straight_imp_measure_pi:
  assumes "B_X \<in> Bundle" "g \<in> B_X" "h \<in> B_X" "\<phi> \<in> (Acoord B_X)" "\<exists> l \<in> Line. g \<union> h = l"  
  shows "ameasure_rel \<phi> g h = 2" 
proof -
  define X where "X = endpoint g"
  from assms (1,2,3) have "X = endpoint h" by (subst X_def, rule brossard_bundle2a)
  from assms(1,2) have "g \<in> HalfLine" by (rule brossard_bundle2b) 
  from this halfline_distinct_def endpoint_agrees X_def obtain A where
  g_def:"g = halfline X A" and "A \<noteq> X"
    by force
  from this `g \<in> B_X` have "(halfline X A)\<in> B_X" by simp
  from g_def `g \<in> HalfLine` have "(halfline X A) \<in> HalfLine" by simp
  from assms(1,3) have "h \<in> HalfLine" by (rule brossard_bundle2b) 
  from this halfline_distinct_def endpoint_agrees `X = endpoint h` obtain B where
  h_def:"h = halfline X B" and "B \<noteq> X"
    by force 
  from assms(1) assms(2) assms(4) g_def 
  have "0 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 4" by (rule_tac acoordfn_bounds, auto)
  consider "0 \<le> mod4 (\<phi> (halfline X A)) \<and> mod4 (\<phi> (halfline X A)) < 2" |
"2\<le> mod4 (\<phi> (halfline X A)) \<and> mod4 (\<phi> (halfline X A)) < 4" using mod4_bestdef
    by force
  then show ?thesis
  proof (cases)
    assume assm1: "0 \<le> mod4 (\<phi> (halfline X A)) \<and> mod4 (\<phi> (halfline X A)) < 2"
    from this `0 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 4`
    have "0 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 2"
      by (simp add: mod4_simple)
    obtain c where "0\<le>c \<and> c <4" and "c =4 mod4 (\<phi> (halfline X A) + 2)" using eq4_ex_unique eq4_sym
      by meson
    then have "c = mod4 (\<phi> (halfline X A) + 2)"
      using eq4_imp_eq mod4_bestdef(1) mod4_bestdef(2) by blast
    from this have " 0 \<le> c \<and> c < 4" using mod4_bestdef by simp
    from this `0 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 2` `c = mod4 (\<phi> (halfline X A) + 2)`
    have "c = \<phi> (halfline X A) + 2" using mod4_bestdef assm1 
      by (rule_tac eq4_imp_eq, auto simp: eqmod4_imp_eq4)
    from `B_X \<in> Bundle` `\<phi> \<in> Acoord B_X` `0 \<le> c \<and> c < 4`
    have "\<exists>!hC. hC \<in> B_X \<and> \<phi> hC = c" by (rule_tac halfline_with_measure_r)
    then obtain hC where "hC \<in> B_X" and "\<phi> hC = c" by blast
    from this `B_X \<in> Bundle` have "hC \<in> HalfLine" by (rule_tac brossard_bundle2b)
    then obtain C where "endpoint hC \<noteq> C" "(halfline (endpoint hC) C) = hC" 
      using endpoint_halfline_def
      by metis
    from this `hC \<in> B_X` have "(halfline X C) = hC"
      using `X = endpoint h` `h \<in> B_X` brossard_bundle2a
      by (metis assms(1))
    from this `hC \<in> B_X` have "(halfline X C) \<in> B_X" by simp
    have "endpoint (halfline X A) = endpoint (halfline X C)" using endpoint_agrees by simp
    from `(halfline X C) = hC` `hC \<in> HalfLine` have "(halfline X C) \<in> HalfLine" by simp
    from `(halfline X C) = hC` `\<phi> hC = c` `c = \<phi> (halfline X A) + 2`  
    have "\<phi> (halfline X C) = \<phi> (halfline X A) + 2" by simp
    from this have "\<phi> (halfline X C) - \<phi> (halfline X A) = \<phi> (halfline X A) + 2 -\<phi> (halfline X A)"
      by simp
    also have "... = 2" by simp
    finally have  "\<phi> (halfline X C) - \<phi> (halfline X A) = 2" by simp
    then have mod4XCA:"mod4(\<phi> (halfline X C) - \<phi> (halfline X A)) = 2"
      using mod4_simple by fastforce
    have "mod4(\<phi> (halfline X A) - \<phi> (halfline X C)) 
= mod4( -(\<phi> (halfline X C) - \<phi> (halfline X A)))" 
      by simp
    also have "...  = mod4( - mod4 (\<phi> (halfline X C) - \<phi> (halfline X A)))" by (rule mod4_neg)
    also have "...  = mod4( - 2)"by (subst mod4XCA, rule refl)
    finally have "mod4(\<phi> (halfline X A) - \<phi> (halfline X C)) = 2" by (subst(asm) mod4_2_inv)
    from this mod4XCA have straight_angle:"ameasure_rel \<phi> (halfline X C) (halfline X A) = 2"
      using ameasure_rel_def `B_X \<in> Bundle`
    `(halfline X C) \<in> B_X` `(halfline X A)\<in> B_X` `(halfline X C) \<in> HalfLine`
    `(halfline X A) \<in> HalfLine` `endpoint (halfline X A) = endpoint (halfline X C)`[symmetric]
    `\<phi> \<in> Acoord B_X` by force
    from straight_angle `B_X \<in> Bundle` `halfline X A \<in> B_X` `halfline X C \<in> B_X` `\<phi> \<in> Acoord B_X` 
    have "\<exists>l\<in>Line. (halfline X C) \<union> (halfline X A)  = l" using pi_imp_straight
      by presburger
    then obtain l1 where "l1 \<in> Line" and l1_def : "(halfline X C) \<union> (halfline X A)  = l1" by blast
    from `\<exists> l \<in> Line. g \<union> h = l` g_def h_def have "\<exists>l\<in>Line. (halfline X B) \<union> (halfline X A)  = l" 
      by (simp add: Un_commute)
    then obtain l2 where "l2 \<in> Line" and l2_def: "(halfline X B) \<union> (halfline X A)  = l2" by blast
    from l1_def l2_def `l1 \<in> Line` `l2 \<in> Line` `A\<noteq>X` have "l1 = line A X" "l2 = line A X"
      using line_bestdef_inv
      by (meson halfline_bestdef Un_iff)+
    from `l1 = line A X` l1_def have "C \<in> line A X"
      using halfline_bestdef(1) by fastforce
    from \<open>endpoint hC \<noteq> C\<close> \<open>halfline X C = hC\<close> have "X \<noteq> C" using endpoint_agrees try0
        by blast
    have "(halfline X C) = (halfline X B)" 
    proof (rule halfline_independence[rotated], rule `B \<noteq> X`)
      from assms(1) assms(4) \<open>halfline X A \<in> B_X\<close>
      have measureXA:"ameasure_rel \<phi> (halfline X A) (halfline X A) = 0" 
        by (subst coinciding_halflines[symmetric], auto)
      from this straight_angle have "(halfline X A) \<noteq> (halfline X C)" by fastforce
      have "2 \<noteq> (0::real)"
        by auto
      have C_where:"C \<in> halfline X B \<or> C \<in> halfline X A"
        using \<open>C \<in> line A X\<close> \<open>l2 = line A X\<close>  l2_def Un_iff by blast
      have "C \<notin> halfline X A" using `(halfline X A) \<noteq> (halfline X C)`
        using \<open>X \<noteq> C\<close> halfline_independence by blast
      then show "B \<in> halfline X C"
        using  C_where  \<open>X \<noteq> C\<close> halfline_bestdef(1) halfline_independence by blast
    qed
    from `(halfline X C) \<in> B_X` this have "(halfline X B) \<in> B_X" by simp
    from halfline_bestdef `halfline X A \<in> HalfLine` 
 `\<phi> \<in> Acoord B_X` `(halfline X B) \<in> B_X`
 `(halfline X A) \<in> B_X` `B_X \<in> Bundle`
    have "ameasure_rel \<phi> (halfline X C) (halfline X A) 
= ameasure_rel \<phi> (halfline X A) (halfline X B)" 
      by (subst `(halfline X C) = (halfline X B)`,
rule_tac ameasure_rel_commutes,auto simp: endpoint_agrees)
    from this straight_angle g_def h_def show ?thesis
      by simp
  next
    assume assm2:"2\<le> mod4 (\<phi> (halfline X A)) \<and> mod4 (\<phi> (halfline X A)) < 4"
    from this `0 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 4`
    have "2 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 4"
      by (simp add: mod4_simple)
    obtain d where "0\<le>d \<and> d <4" and "d =4 mod4 (\<phi> (halfline X A) - 2)" using eq4_ex_unique eq4_sym
      by meson
    then have "d = mod4 (\<phi> (halfline X A) - 2)"
      using eq4_imp_eq mod4_bestdef(1) mod4_bestdef(2) by blast
    from this have " 0 \<le> d \<and> d < 4" using mod4_bestdef by simp
    from this `2 \<le> \<phi> (halfline X A) \<and> \<phi> (halfline X A) < 4` `d = mod4 (\<phi> (halfline X A) - 2)`
    have "d = \<phi> (halfline X A) - 2" using mod4_bestdef assm2 
      by (rule_tac eq4_imp_eq, auto simp: eqmod4_imp_eq4)
    from `B_X \<in> Bundle` `\<phi> \<in> Acoord B_X` `0 \<le> d \<and> d < 4`
    have "\<exists>!hC. hC \<in> B_X \<and> \<phi> hC = d" by (rule_tac halfline_with_measure_r)
    then obtain hD where "hD \<in> B_X" and "\<phi> hD = d" by blast
    from this `B_X \<in> Bundle` have "hD \<in> HalfLine" by (rule_tac brossard_bundle2b)
    then obtain D where "endpoint hD \<noteq> D" "(halfline (endpoint hD) D) = hD" 
      using endpoint_halfline_def
      by metis
    from this `hD \<in> B_X` have "(halfline X D) = hD" using `X = endpoint h` `h \<in> B_X` 
brossard_bundle2a
      by (metis assms(1))
    from this `hD \<in> B_X` have "(halfline X D) \<in> B_X" by simp
    have "endpoint (halfline X A) = endpoint (halfline X D)" using endpoint_agrees by simp
    from `(halfline X D) = hD` `hD \<in> HalfLine` have "(halfline X D) \<in> HalfLine" by simp
    from `(halfline X D) = hD` `\<phi> hD = d` `d = \<phi> (halfline X A) - 2`
    have "\<phi> (halfline X D) = \<phi> (halfline X A) - 2" by simp
    from this have "\<phi> (halfline X D) - \<phi> (halfline X A) = \<phi> (halfline X A) - 2 -\<phi> (halfline X A)"
      by simp
    also have "... = - 2" by (simp)
    finally have  "\<phi> (halfline X D) - \<phi> (halfline X A) = - 2" by simp
    then have mod4XCA:"mod4(\<phi> (halfline X D) - \<phi> (halfline X A)) = 2" 
      using mod4_simple by fastforce
    have "mod4(\<phi> (halfline X A) - \<phi> (halfline X D))
 = mod4( -(\<phi> (halfline X D) - \<phi> (halfline X A)))" 
      by simp
    also have "...  = mod4( - mod4 (\<phi> (halfline X D) - \<phi> (halfline X A)))" by (rule mod4_neg)
    also have "...  = mod4( - 2)"by (subst mod4XCA, rule refl)
    finally have "mod4(\<phi> (halfline X A) - \<phi> (halfline X D)) = 2" by (subst(asm) mod4_2_inv)
    from this mod4XCA have straight_angle:"ameasure_rel \<phi> (halfline X D) (halfline X A) = 2"
      using ameasure_rel_def `B_X \<in> Bundle`
    `(halfline X D) \<in> B_X` `(halfline X A)\<in> B_X` `(halfline X D) \<in> HalfLine`
    `(halfline X A) \<in> HalfLine` `endpoint (halfline X A) = endpoint (halfline X D)`[symmetric]
    `\<phi> \<in> Acoord B_X` by force
    from straight_angle `B_X \<in> Bundle` `halfline X A \<in> B_X` `halfline X D \<in> B_X` `\<phi> \<in> Acoord B_X` 
    have "\<exists>l\<in>Line. (halfline X D) \<union> (halfline X A)  = l" using pi_imp_straight
      by presburger
    then obtain l1 where "l1 \<in> Line" and l1_def : "(halfline X D) \<union> (halfline X A)  = l1" by blast
    from `\<exists> l \<in> Line. g \<union> h = l` g_def h_def have "\<exists>l\<in>Line. (halfline X B) \<union> (halfline X A)  = l" 
      by (simp add: Un_commute)
    then obtain l2 where "l2 \<in> Line" and l2_def: "(halfline X B) \<union> (halfline X A)  = l2" by blast
    from l1_def l2_def `l1 \<in> Line` `l2 \<in> Line` `A\<noteq>X` have "l1 = line A X" "l2 = line A X"
      using line_bestdef_inv
      by (meson halfline_bestdef Un_iff)+
    from `l1 = line A X` l1_def have "D \<in> line A X"
      using halfline_bestdef(1) by fastforce
    from \<open>endpoint hD \<noteq> D\<close> \<open>halfline X D = hD\<close> have "X \<noteq> D" using endpoint_agrees
        by blast
    have "(halfline X D) = (halfline X B)" 
    proof (rule halfline_independence[rotated], rule `B \<noteq> X`)
      from assms(1) assms(4) \<open>halfline X A \<in> B_X\<close> 
      have measureXA:"ameasure_rel \<phi> (halfline X A) (halfline X A) = 0" 
        by (subst coinciding_halflines[symmetric], auto)
      from this straight_angle have "(halfline X A) \<noteq> (halfline X D)" by fastforce
      have "2 \<noteq> (0::real)"
        by auto
      have D_where:"D \<in> halfline X B \<or> D \<in> halfline X A"
        using \<open>D \<in> line A X\<close> \<open>l2 = line A X\<close>  l2_def Un_iff by blast
      have "D \<notin> halfline X A" using `(halfline X A) \<noteq> (halfline X D)`
        using \<open>X \<noteq> D\<close> halfline_independence by blast
      then show "B \<in> halfline X D"
        using  D_where  \<open>X \<noteq> D\<close> halfline_bestdef(1) halfline_independence by blast
    qed
    from `(halfline X D) \<in> B_X` this have "(halfline X B) \<in> B_X" by simp
    from halfline_bestdef `halfline X A \<in> HalfLine` 
 `\<phi> \<in> Acoord B_X` `(halfline X B) \<in> B_X`
 `(halfline X A) \<in> B_X` `B_X \<in> Bundle`
    have "ameasure_rel \<phi> (halfline X D) (halfline X A)
 = ameasure_rel \<phi> (halfline X A) (halfline X B)" 
      by (subst `(halfline X D) = (halfline X B)`,
rule_tac ameasure_rel_commutes,auto simp: endpoint_agrees)
    from this straight_angle g_def h_def show ?thesis
      by simp    
  qed
qed


lemma sameside_halflines_share_points: 
  assumes "q \<in> HalfLine" "h \<in> HalfLine" "g \<in> HalfLine" "l \<in> Line" "q \<union> h = l" "g \<union> h = l"
  shows "\<exists>A B. A \<in> q \<and> A \<in> g \<and> B \<in> q \<and> B \<in> g \<and> A \<noteq> B"
proof -
  (*there are at least two points on the line that are not on h*)
  from `h \<in> HalfLine` obtain X A where h_def:"h = halfline X A" "A \<noteq> X"
    using halfline_distinct_def by blast 
  then have h_set: "h = {P. \<not> between A X P \<and> P \<in> line X A}" using halfline_def by auto
  from `A \<noteq> X` have "\<exists>B\<in>line X A. between A X B" by (rule between_otherside)
  then obtain B where "B\<in>line X A" "between A X B" by blast
  from this h_set have "B \<notin> h" by auto
  from `between A X B` have "A \<noteq> B" "X \<noteq> B" by (rule_tac [!] bet_imp_distinct)
  from `X \<noteq> B` have "\<exists>C\<in>line B X. between X B C" by (rule between_otherside)
  then obtain C where "C\<in>line B X" "between X B C" by blast
  from `B\<in>line X A` `X \<noteq> B`[symmetric] line_bestdef have "line X A = line B X"
    by (rule_tac line_bestdef_inv)
  from `between X B C` have "B \<noteq> C" by (rule_tac [!] bet_imp_distinct)
  from `between A X B` have "between B X A" by (subst between_sym)
  from `between X B C` have "between C B X" by (subst between_sym)
  from this `between B X A` have "between C X A" by (rule between_trans(1))
  from this have "between A X C" by (subst between_sym)
  from this h_set have "C \<notin> h" by auto
  from `q \<union> h = l`  have "A \<in> l" "X \<in> l" using halfline_bestdef h_def by blast+
  from `l \<in> Line` `A \<in> l` `X \<in> l` `A \<noteq> X`[symmetric] line_bestdef 
  have " l = line X A"  by (rule_tac line_bestdef_inv)
  have "B \<in> line X A" using `line X A = line B X` line_bestdef by simp
  from `between A X C` have "C \<in> line X A" by (subst line_sym, rule_tac between_imp_collinear)  
  from this `B \<in> line X A` `l = line X A` `q \<union> h = l` `C \<notin> h` `B \<notin> h` `g \<union> h = l`
  have "C \<in> q \<and> C \<in> g \<and> B \<in> q \<and> B \<in> g" by auto
  from this `B \<noteq> C` show ?thesis by blast
qed

lemma otherhalf_welldefined: (*proof is exactly the same as
 that of the next theorem, and is different
but equivalent to that of otherhalf_bestdef*)
  assumes "h \<in> HalfLine" shows "\<exists>!g. g \<in> HalfLine \<and> endpoint h 
= endpoint g \<and> (\<exists>l\<in>Line. g \<union> h = l)"
proof -
  from assms have "\<exists>B\<in>Bundle. h \<in> B" by (rule brossard_bundle1_single)
  then obtain B where "B \<in> Bundle" "h\<in>B" by blast
  from `B \<in> Bundle` obtain \<phi> where phi_def: "\<phi> \<in> Acoord B" 
    by (rule_tac exE, rule brossard_angle_measure1)
  from `B \<in> Bundle` phi_def have "bij_betw \<phi> B {x. 0 \<le> x \<and> x < 4}"
    by (rule brossard_angle_measure2)
  from this have "\<phi> ` B = {x. 0 \<le> x \<and> x < 4}" 
    by (subst(asm) bij_betw_def, rule_tac conjunct2)
  from this have im:"{y. \<exists>z\<in>B. y = \<phi> z} = {x. 0 \<le> x \<and> x < 4}" by (subst(asm) image_def)
  show ?thesis
  proof (cases "\<phi> h < 2")
    assume "\<not> \<phi> h < 2"
    then have "\<phi> h \<ge> 2" by simp
    from `h \<in> B` `image \<phi> B = {x. 0 \<le> x \<and> x < 4}`
    have "\<phi> h \<in> {x. 0 \<le> x \<and> x < 4}" by blast
    from this `\<phi> h \<ge> 2` have "2 \<le> \<phi> h \<and> \<phi> h < 4" by blast
    then have "\<phi> h - (2::real) \<in> {x. 0 \<le> x \<and> x < 4}" by fastforce
    from im this obtain g where "g \<in> B" and "\<phi> h - (2::real) = \<phi> g" by blast
    then have "\<phi> h - \<phi> g = (2::real)" by simp
    have "0\<le>(2::real) \<and> (2::real)<4" by simp
    from `\<phi> h - \<phi> g = (2::real)` this have "mod4 (\<phi> h - \<phi> g) = (2::real)" 
      by (subst `\<phi> h - \<phi> g = (2::real)`,rule_tac mod4_simple)
    from `\<phi> h - \<phi> g = (2::real)` have "\<phi> g - \<phi> h = -(2::real)" by simp
    then have "\<phi> g - \<phi> h =4 -(2::real)" by (subst `\<phi> g - \<phi> h = -(2::real)`, rule_tac eq4_refl)
    then have "\<phi> g - \<phi> h =4 -(2::real)+ real_of_int (4 * 1)" by (rule eq4_bestdef)
    then have "\<phi> g - \<phi> h =4 (2::real)" by force
    from `0\<le>(2::real) \<and> (2::real)<4` this have "mod4 (\<phi> g - \<phi> h) = (2::real)"
      by (rule eq4_imp_eq_mod4)
    from `B \<in> Bundle` `g \<in> B` `h \<in> B` have "g \<in> HalfLine" "endpoint g = endpoint h" 
      by (rule_tac[2] brossard_bundle2a, rule_tac [1] brossard_bundle2b)
    from `g \<in> HalfLine` `h \<in> HalfLine` `endpoint g = endpoint h` `\<phi> \<in> Acoord B` `g \<in> B`
    `h \<in> B` `B \<in> Bundle`
    have "ameasure_rel \<phi> g h = min (mod4 (\<phi> g - \<phi> h)) (mod4 (\<phi> h - \<phi> g))" 
      by (rule ameasure_rel_def)
    from this `mod4 (\<phi> h - \<phi> g) = (2::real)` `mod4 (\<phi> g - \<phi> h) = (2::real)`
    have "ameasure_rel \<phi> g h = 2" by simp
    from `B \<in> Bundle` `g \<in> B` `h \<in> B` `\<phi> \<in> Acoord B` this 
    have "\<exists>l\<in>Line. g \<union> h = l" by (rule_tac pi_imp_straight)
    then obtain l1 where l1_def: "l1\<in>Line"  "g \<union> h = l1" by blast
    have "\<forall>q. (q \<in> HalfLine \<and> endpoint h = endpoint q \<and> (\<exists>l\<in>Line. q \<union> h = l)) \<longrightarrow> q = g" 
    proof (rule allI, rule impI, (erule conjE)+)
      fix q assume "\<exists>l\<in>Line. q \<union> h = l" "q \<in> HalfLine" "endpoint h = endpoint q"
      then obtain l2 where "l2\<in>Line"  "q \<union> h = l2" by blast
      from this unique_line_halfline l1_def have "l1 = l2"
        using `h \<in> HalfLine` by blast
      from `h \<in> HalfLine` obtain X A where h_def:"h = halfline X A" "A \<noteq> X"
        using halfline_distinct_def by blast 
      from `g \<in> HalfLine` obtain Y C where g_def:"g = halfline Y C" "C \<noteq> Y"
        using halfline_distinct_def by blast 
      have "Y = X" using `endpoint g = endpoint h` h_def g_def endpoint_agrees by auto
      from this g_def have g_def:"g = halfline X C" "C \<noteq> X" by auto
      from `q \<in> HalfLine` obtain Xx Bb where q_def:"q = halfline Xx Bb" "Bb \<noteq> Xx"
        using halfline_distinct_def by blast 
      have "Xx = X" using `endpoint h = endpoint q` h_def q_def endpoint_agrees by auto
      from this q_def have q_def:"q = halfline X Bb" "Bb \<noteq> X" by auto
      then have "X \<in> q" using halfline_bestdef by simp
      from g_def have "X \<in> g" using halfline_bestdef by simp
      from `q \<in> HalfLine` `h \<in> HalfLine` `g \<in> HalfLine` `q \<union> h = l2` `g \<union> h = l1`
 `l1 = l2` `X \<in> q`
      `X \<in> g` 
      have "\<exists>B. B \<in> q \<and> B \<in> g \<and> B \<noteq> X" using sameside_halflines_share_points
        by (metis \<open>l2 \<in> Line\<close>)
      then obtain B where "B \<in> q" "B \<in> g" "B \<noteq> X" by blast
      from this q_def have q_def:"q = halfline X B"
        using halfline_independence by blast
      moreover from `B \<in> g` `B \<noteq> X` g_def have g_def:"g = halfline X B"
        using halfline_independence by blast
      ultimately show "q=g" by simp
    qed
    from this `\<exists>l\<in>Line. g \<union> h = l` `g \<in> HalfLine`  `endpoint g = endpoint h`
    show ?thesis by metis
  next
    assume "\<phi> h < 2"
    from `h \<in> B` `image \<phi> B = {x. 0 \<le> x \<and> x < 4}`
    have "\<phi> h \<in> {x. 0 \<le> x \<and> x < 4}" by blast
    from this `\<phi> h < 2` have "0 \<le> \<phi> h \<and> \<phi> h < 2" by blast
    then have "\<phi> h + (2::real) \<in> {x. 0 \<le> x \<and> x < 4}" by fastforce
    from im this obtain g where "g \<in> B" and "\<phi> h + (2::real) = \<phi> g" by blast
    then have "\<phi> g - \<phi> h = (2::real)" by simp
    then have "\<phi> g - \<phi> h =4 (2::real)" by (simp add: eq4_refl)
    have "0\<le>(2::real) \<and> (2::real)<4" by linarith
    from `\<phi> g - \<phi> h =4 (2::real)` this have "mod4 (\<phi> g - \<phi> h) = (2::real)"
      by (rule_tac eq4_imp_eq_mod4)
    from `\<phi> h + (2::real) = \<phi> g` have "\<phi> h - \<phi> g = - (2::real)" by simp
    then have "\<phi> h - \<phi> g =4 -(2::real)" by (subst `\<phi> h - \<phi> g = -(2::real)`, rule_tac eq4_refl)
    then have "\<phi> h - \<phi> g =4 -(2::real)+ real_of_int (4 * 1)" by (rule eq4_bestdef)
    then have "\<phi> h - \<phi> g =4 (2::real)" by force
    from `0\<le>(2::real) \<and> (2::real)<4` this have "mod4 (\<phi> h - \<phi> g) = (2::real)"
      by (rule eq4_imp_eq_mod4)
    from `B \<in> Bundle` `g \<in> B` `h \<in> B` have "g \<in> HalfLine" "endpoint g = endpoint h" 
      by (rule_tac[2] brossard_bundle2a, rule_tac [1] brossard_bundle2b)
    from `g \<in> HalfLine` `h \<in> HalfLine` `endpoint g = endpoint h` `\<phi> \<in> Acoord B` `g \<in> B`
    `h \<in> B` `B \<in> Bundle`
    have "ameasure_rel \<phi> g h = min (mod4 (\<phi> g - \<phi> h)) (mod4 (\<phi> h - \<phi> g))" 
      by (rule ameasure_rel_def)
    from this `mod4 (\<phi> h - \<phi> g) = (2::real)` `mod4 (\<phi> g - \<phi> h) = (2::real)`
    have "ameasure_rel \<phi> g h = 2" by simp
    from `B \<in> Bundle` `g \<in> B` `h \<in> B` `\<phi> \<in> Acoord B` this 
    have "\<exists>l\<in>Line. g \<union> h = l" by (rule_tac pi_imp_straight)
    then obtain l1 where l1_def: "l1\<in>Line"  "g \<union> h = l1" by blast
    have "\<forall>q. (q \<in> HalfLine \<and> endpoint h = endpoint q \<and> (\<exists>l\<in>Line. q \<union> h = l)) \<longrightarrow> q = g" 
    proof (rule allI, rule impI, (erule conjE)+)
      fix q assume "\<exists>l\<in>Line. q \<union> h = l" "q \<in> HalfLine" "endpoint h = endpoint q"
      then obtain l2 where "l2\<in>Line"  "q \<union> h = l2" by blast
      from this unique_line_halfline l1_def have "l1 = l2"
        using `h \<in> HalfLine` by blast
      from `h \<in> HalfLine` obtain X A where h_def:"h = halfline X A" "A \<noteq> X"
        using halfline_distinct_def by blast 
      from `g \<in> HalfLine` obtain Y C where g_def:"g = halfline Y C" "C \<noteq> Y"
        using halfline_distinct_def by blast 
      have "Y = X" using `endpoint g = endpoint h` h_def g_def endpoint_agrees by auto
      from this g_def have g_def:"g = halfline X C" "C \<noteq> X" by auto
      from `q \<in> HalfLine` obtain Xx Bb where q_def:"q = halfline Xx Bb" "Bb \<noteq> Xx"
        using halfline_distinct_def by blast 
      have "Xx = X" using `endpoint h = endpoint q` h_def q_def endpoint_agrees by auto
      from this q_def have q_def:"q = halfline X Bb" "Bb \<noteq> X" by auto
      then have "X \<in> q" using halfline_bestdef by simp
      from g_def have "X \<in> g" using halfline_bestdef by simp
      from `q \<in> HalfLine` `h \<in> HalfLine` `g \<in> HalfLine` `q \<union> h = l2` 
`g \<union> h = l1` `l1 = l2` `X \<in> q`
      `X \<in> g` 
      have "\<exists>B. B \<in> q \<and> B \<in> g \<and> B \<noteq> X" using sameside_halflines_share_points
        by (metis \<open>l2 \<in> Line\<close>)
      then obtain B where "B \<in> q" "B \<in> g" "B \<noteq> X" by blast
      from this q_def have q_def:"q = halfline X B"
        using halfline_independence by blast
      moreover from `B \<in> g` `B \<noteq> X` g_def have g_def:"g = halfline X B"
        using halfline_independence by blast
      ultimately show "q=g" by simp
    qed
    from this `\<exists>l\<in>Line. g \<union> h = l` `g \<in> HalfLine`  `endpoint g = endpoint h`
    show ?thesis by metis
  qed
qed

lemma bundle_both_halves: assumes "B\<in>Bundle" "h \<in> B" "h \<in> HalfLine" shows "(otherhalf h) \<in> B"
proof -
(*we need to show that angle 2 gives a straight line for this?*)
  from `h \<in> HalfLine` have otherhalf_char:"endpoint h = endpoint (otherhalf h)"
    "\<exists>l\<in>Line. otherhalf h \<union> h = l" "otherhalf h \<in> HalfLine" by (rule_tac [!] otherhalf_bestdef)
  from assms(1) obtain \<phi> where phi_def: "\<phi> \<in> Acoord B"
    by (rule_tac exE, rule brossard_angle_measure1)
  from assms(1) phi_def have "bij_betw \<phi> B {x. 0 \<le> x \<and> x < 4}" by (rule brossard_angle_measure2)
  from this have "\<phi> ` B = {x. 0 \<le> x \<and> x < 4}" 
    by (subst(asm) bij_betw_def, rule_tac conjunct2)
  from this have im:"{y. \<exists>z\<in>B. y = \<phi> z} = {x. 0 \<le> x \<and> x < 4}" by (subst(asm) image_def)
  show ?thesis
  proof (cases "\<phi> h < 2")
    assume "\<not> \<phi> h < 2"
    then have "\<phi> h \<ge> 2" by simp
    from `h \<in> B` `image \<phi> B = {x. 0 \<le> x \<and> x < 4}`
    have "\<phi> h \<in> {x. 0 \<le> x \<and> x < 4}" by blast
    from this `\<phi> h \<ge> 2` have "2 \<le> \<phi> h \<and> \<phi> h < 4" by blast
    then have "\<phi> h - (2::real) \<in> {x. 0 \<le> x \<and> x < 4}" by fastforce
    from im this obtain g where "g \<in> B" and "\<phi> h - (2::real) = \<phi> g" by blast
    then have "\<phi> h - \<phi> g = (2::real)" by simp
    have "0\<le>(2::real) \<and> (2::real)<4" by simp
    from `\<phi> h - \<phi> g = (2::real)` this have "mod4 (\<phi> h - \<phi> g) = (2::real)" 
      by (subst `\<phi> h - \<phi> g = (2::real)`,rule_tac mod4_simple)
    from `\<phi> h - \<phi> g = (2::real)` have "\<phi> g - \<phi> h = -(2::real)" by simp
    then have "\<phi> g - \<phi> h =4 -(2::real)" by (subst `\<phi> g - \<phi> h = -(2::real)`, rule_tac eq4_refl)
    then have "\<phi> g - \<phi> h =4 -(2::real)+ real_of_int (4 * 1)" by (rule eq4_bestdef)
    then have "\<phi> g - \<phi> h =4 (2::real)" by force
    from `0\<le>(2::real) \<and> (2::real)<4` this have "mod4 (\<phi> g - \<phi> h) = (2::real)"
      by (rule eq4_imp_eq_mod4)
    from `B \<in> Bundle` `g \<in> B` `h \<in> B` have "g \<in> HalfLine" "endpoint g = endpoint h" 
      by (rule_tac[2] brossard_bundle2a, rule_tac [1] brossard_bundle2b)
    from `g \<in> HalfLine` `h \<in> HalfLine` `endpoint g = endpoint h` `\<phi> \<in> Acoord B` `g \<in> B`
    `h \<in> B` `B \<in> Bundle`
    have "ameasure_rel \<phi> g h = min (mod4 (\<phi> g - \<phi> h)) (mod4 (\<phi> h - \<phi> g))" 
      by (rule ameasure_rel_def)
    from this `mod4 (\<phi> h - \<phi> g) = (2::real)` `mod4 (\<phi> g - \<phi> h) = (2::real)`
    have "ameasure_rel \<phi> g h = 2" by simp
    from `B \<in> Bundle` `g \<in> B` `h \<in> B` `\<phi> \<in> Acoord B` this 
    have "\<exists>l\<in>Line. g \<union> h = l" by (rule_tac pi_imp_straight)
    then obtain l1 where l1_def: "l1\<in>Line"  "g \<union> h = l1" by blast
    have "\<forall>q. (q \<in> HalfLine \<and> endpoint h = endpoint q \<and> (\<exists>l\<in>Line. q \<union> h = l)) \<longrightarrow> q = g" 
    proof (rule allI, rule impI, (erule conjE)+)
      fix q assume "\<exists>l\<in>Line. q \<union> h = l" "q \<in> HalfLine" "endpoint h = endpoint q"
      then obtain l2 where "l2\<in>Line"  "q \<union> h = l2" by blast
      from this unique_line_halfline l1_def have "l1 = l2"
        using `h \<in> HalfLine` by blast
      from `h \<in> HalfLine` obtain X A where h_def:"h = halfline X A" "A \<noteq> X"
        using halfline_distinct_def by blast 
      from `g \<in> HalfLine` obtain Y C where g_def:"g = halfline Y C" "C \<noteq> Y"
        using halfline_distinct_def by blast 
      have "Y = X" using `endpoint g = endpoint h` h_def g_def endpoint_agrees by auto
      from this g_def have g_def:"g = halfline X C" "C \<noteq> X" by auto
      from `q \<in> HalfLine` obtain Xx Bb where q_def:"q = halfline Xx Bb" "Bb \<noteq> Xx"
        using halfline_distinct_def by blast 
      have "Xx = X" using `endpoint h = endpoint q` h_def q_def endpoint_agrees by auto
      from this q_def have q_def:"q = halfline X Bb" "Bb \<noteq> X" by auto
      then have "X \<in> q" using halfline_bestdef by simp
      from g_def have "X \<in> g" using halfline_bestdef by simp
      from `q \<in> HalfLine` `h \<in> HalfLine` `g \<in> HalfLine` `q \<union> h = l2` `g \<union> h = l1` 
`l1 = l2` `X \<in> q`
      `X \<in> g` 
      have "\<exists>B. B \<in> q \<and> B \<in> g \<and> B \<noteq> X" using sameside_halflines_share_points
        by (metis \<open>l2 \<in> Line\<close>)
      then obtain B where "B \<in> q" "B \<in> g" "B \<noteq> X" by blast
      from this q_def have q_def:"q = halfline X B"
        using halfline_independence by blast
      moreover from `B \<in> g` `B \<noteq> X` g_def have g_def:"g = halfline X B"
        using halfline_independence by blast
      ultimately show "q=g" by simp
    qed
    from this `\<exists>l\<in>Line. g \<union> h = l` `g \<in> HalfLine`  `endpoint g = endpoint h` otherhalf_char
    have "otherhalf h = g"
      by presburger
    from this `g\<in>B` show "(otherhalf h) \<in>B" by simp
  next
    assume "\<phi> h < 2" 
    from `h \<in> B` `image \<phi> B = {x. 0 \<le> x \<and> x < 4}`
    have "\<phi> h \<in> {x. 0 \<le> x \<and> x < 4}" by blast
    from this `\<phi> h < 2` have "0 \<le> \<phi> h \<and> \<phi> h < 2" by blast
    then have "\<phi> h + (2::real) \<in> {x. 0 \<le> x \<and> x < 4}" by fastforce
    from im this obtain g where "g \<in> B" and "\<phi> h + (2::real) = \<phi> g" by blast
    then have "\<phi> g - \<phi> h = (2::real)" by simp
    then have "\<phi> g - \<phi> h =4 (2::real)" by (simp add: eq4_refl)
    have "0\<le>(2::real) \<and> (2::real)<4" by linarith
    from `\<phi> g - \<phi> h =4 (2::real)` this have "mod4 (\<phi> g - \<phi> h) = (2::real)"
      by (rule_tac eq4_imp_eq_mod4)
    from `\<phi> h + (2::real) = \<phi> g` have "\<phi> h - \<phi> g = - (2::real)" by simp
    then have "\<phi> h - \<phi> g =4 -(2::real)" by (subst `\<phi> h - \<phi> g = -(2::real)`, rule_tac eq4_refl)
    then have "\<phi> h - \<phi> g =4 -(2::real)+ real_of_int (4 * 1)" by (rule eq4_bestdef)
    then have "\<phi> h - \<phi> g =4 (2::real)" by force
    from `0\<le>(2::real) \<and> (2::real)<4` this have "mod4 (\<phi> h - \<phi> g) = (2::real)"
      by (rule eq4_imp_eq_mod4)
    from `B \<in> Bundle` `g \<in> B` `h \<in> B` have "g \<in> HalfLine" "endpoint g = endpoint h" 
      by (rule_tac[2] brossard_bundle2a, rule_tac [1] brossard_bundle2b)
    from `g \<in> HalfLine` `h \<in> HalfLine` `endpoint g = endpoint h` `\<phi> \<in> Acoord B` `g \<in> B`
    `h \<in> B` `B \<in> Bundle`
    have "ameasure_rel \<phi> g h = min (mod4 (\<phi> g - \<phi> h)) (mod4 (\<phi> h - \<phi> g))" 
      by (rule ameasure_rel_def)
    from this `mod4 (\<phi> h - \<phi> g) = (2::real)` `mod4 (\<phi> g - \<phi> h) = (2::real)`
    have "ameasure_rel \<phi> g h = 2" by simp
    from `B \<in> Bundle` `g \<in> B` `h \<in> B` `\<phi> \<in> Acoord B` this 
    have "\<exists>l\<in>Line. g \<union> h = l" by (rule_tac pi_imp_straight)
    then obtain l1 where l1_def: "l1\<in>Line"  "g \<union> h = l1" by blast
    have "\<forall>q. (q \<in> HalfLine \<and> endpoint h = endpoint q \<and> (\<exists>l\<in>Line. q \<union> h = l)) \<longrightarrow> q = g" 
    proof (rule allI, rule impI, (erule conjE)+)
      fix q assume "\<exists>l\<in>Line. q \<union> h = l" "q \<in> HalfLine" "endpoint h = endpoint q"
      then obtain l2 where "l2\<in>Line"  "q \<union> h = l2" by blast
      from this unique_line_halfline l1_def have "l1 = l2"
        using `h \<in> HalfLine` by blast
      from `h \<in> HalfLine` obtain X A where h_def:"h = halfline X A" "A \<noteq> X"
        using halfline_distinct_def by blast 
      from `g \<in> HalfLine` obtain Y C where g_def:"g = halfline Y C" "C \<noteq> Y"
        using halfline_distinct_def by blast 
      have "Y = X" using `endpoint g = endpoint h` h_def g_def endpoint_agrees by auto
      from this g_def have g_def:"g = halfline X C" "C \<noteq> X" by auto
      from `q \<in> HalfLine` obtain Xx Bb where q_def:"q = halfline Xx Bb" "Bb \<noteq> Xx"
        using halfline_distinct_def by blast 
      have "Xx = X" using `endpoint h = endpoint q` h_def q_def endpoint_agrees by auto
      from this q_def have q_def:"q = halfline X Bb" "Bb \<noteq> X" by auto
      then have "X \<in> q" using halfline_bestdef by simp
      from g_def have "X \<in> g" using halfline_bestdef by simp
      from `q \<in> HalfLine` `h \<in> HalfLine` `g \<in> HalfLine` `q \<union> h = l2` `g \<union> h = l1`
 `l1 = l2` `X \<in> q`
      `X \<in> g` 
      have "\<exists>B. B \<in> q \<and> B \<in> g \<and> B \<noteq> X" using sameside_halflines_share_points
        by (metis \<open>l2 \<in> Line\<close>)
      then obtain B where "B \<in> q" "B \<in> g" "B \<noteq> X" by blast
      from this q_def have q_def:"q = halfline X B"
        using halfline_independence by blast
      moreover from `B \<in> g` `B \<noteq> X` g_def have g_def:"g = halfline X B"
        using halfline_independence by blast
      ultimately show "q=g" by simp
    qed
    from this `\<exists>l\<in>Line. g \<union> h = l` `g \<in> HalfLine`  `endpoint g = endpoint h` otherhalf_char
    have "otherhalf h = g"
      by presburger
    from this `g\<in>B` show "(otherhalf h) \<in>B" by simp
  qed
qed

definition "B\<in>Bundle \<Longrightarrow> vertex B = (THE X. \<forall>g \<in> B. endpoint g = X)"

lemma bundle_nonempty: assumes "B \<in> Bundle" shows "\<exists>g. g \<in> B"
proof -
  from assms have "\<exists>\<phi>. \<phi> \<in> Acoord B" by (rule brossard_angle_measure1)
  then obtain \<phi> where "\<phi> \<in> Acoord B" by (rule exE)
  have "0 \<le> (0::real) \<and> (0::real) < 4" by linarith
  then show "\<exists>g. g \<in> B"
    using \<open>\<phi> \<in> Acoord B\<close> assms halfline_with_measure_r by blast
qed

lemma vertex_bestdef: assumes "B\<in>Bundle" shows "\<forall>g \<in> B. endpoint g = vertex B"
proof (subst vertex_def, rule assms, rule_tac P ="\<lambda> X. \<forall>g \<in> B. endpoint g = X" in theI')
  from assms obtain g where "g \<in> B" using bundle_nonempty by blast
  {fix h assume "h \<in> B"
  from `B\<in>Bundle` `g \<in> B` `h \<in> B` have "endpoint g = endpoint h" by (rule brossard_bundle2a)}
  then have "\<exists>x. \<forall>g\<in>B. endpoint g = x" by metis
  moreover {fix x y assume "\<forall>g\<in>B. endpoint g = x" "\<forall>g\<in>B. endpoint g = y"
    from this `g \<in> B` have "x = y" by fast }
  ultimately show "\<exists>!x. \<forall>g\<in>B. endpoint g = x" by meson
qed

lemma bundle_bestdef: assumes "g \<in> HalfLine" "h \<in> HalfLine" "endpoint g = endpoint h"
  shows "(bundle g h)\<in> Bundle" "g\<in>bundle g h" " h\<in>bundle g h"
proof -
  consider (a) "g = h" | (b) "\<exists>l \<in> Line. g \<union> h = l" | (c) "g \<noteq> h \<and> \<not>(\<exists>l \<in> Line. g \<union> h = l)"
    by argo
  then have "(bundle g h)\<in> Bundle \<and> g\<in>bundle g h \<and> h\<in>bundle g h" 
  proof (cases)
    assume "g \<noteq> h \<and> \<not>(\<exists>l \<in> Line. g \<union> h = l)"
    from bundle_def have nondeg_bundle_def: "bundle g h = (SOME B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B)" 
      by presburger
    from `g \<noteq> h \<and> \<not>(\<exists>l \<in> Line. g \<union> h = l)` assms  have "\<exists>B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B"
      using brossard_bundle1'
      by meson
    then show "bundle g h \<in> Bundle \<and> g\<in>bundle g h \<and> h\<in>bundle g h"
      by (subst nondeg_bundle_def, subst nondeg_bundle_def, subst nondeg_bundle_def, rule someI_ex)
  next
    assume "\<exists> l \<in> Line. g \<union> h = l" (*construct a point not on the line and take a half line
through it*)  
    from this bundle_def have deg_bundle_def: "bundle g h = (SOME B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B)" 
      by presburger
    from `h \<in> HalfLine` have "\<exists>B \<in> Bundle. h \<in> B" by (rule brossard_bundle1_single)
    then obtain B where B_def:"B \<in> Bundle" "h \<in> B" by blast
    from `h \<in> HalfLine` have "\<exists>l\<in>Line. otherhalf h \<union> h = l" "otherhalf h \<in> HalfLine" 
      "endpoint h = endpoint (otherhalf h)"
      by (rule_tac [!] otherhalf_bestdef)
    from this `\<exists> l \<in> Line. g \<union> h = l` `g \<in> HalfLine` `h \<in> HalfLine` 
`endpoint g = endpoint h`[symmetric]
    have "g = (otherhalf h)"
      using otherhalf_welldefined by blast
    from this `B \<in> Bundle` `h \<in> B` `h \<in> HalfLine` have "g \<in> B" using bundle_both_halves by simp
    from this B_def have "\<exists>B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B" by blast
    from this show "bundle g h \<in> Bundle \<and> g\<in> bundle g h \<and> h\<in>bundle g h"
      by (subst deg_bundle_def, subst deg_bundle_def, subst deg_bundle_def, rule_tac someI_ex)
  next 
    assume "g = h"
    from this bundle_def have deg_bundle_def: "bundle g h = (SOME B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B)" 
      by presburger
    from `g \<in> HalfLine` have "\<exists>B\<in>Bundle. g \<in> B" by (rule brossard_bundle1_single)
     from this `g = h` have "\<exists>B. B \<in> Bundle \<and> g\<in>B \<and> h\<in>B" by blast
    from this show "bundle g h \<in> Bundle \<and> g\<in> bundle g h \<and> h\<in>bundle g h"
      by (subst deg_bundle_def, subst deg_bundle_def, subst deg_bundle_def, rule_tac someI_ex)   
  qed
  then show "bundle g h \<in> Bundle" "g\<in> bundle g h" "h\<in>bundle g h" by blast+
qed

lemma halfline_bundle_bestdef:
 "(bundle (halfline X A) (halfline X B))\<in> Bundle"
 "(halfline X A) \<in>bundle (halfline X A) (halfline X B)"
 "(halfline X B) \<in>bundle (halfline X A) (halfline X B)"
  using bundle_bestdef endpoint_agrees halfline_bestdef
  by auto
  


lemma measure_independent_of_bundle:
  assumes "B \<in> Bundle" "C \<in> Bundle"
"g \<in> B" "h \<in> B" "g \<in> C" "h \<in> C""\<phi> \<in> Acoord B" "\<psi> \<in> Acoord C" 
shows "ameasure_rel \<phi> g h = ameasure_rel \<psi> g h"
proof -
  consider "g = h" | "\<exists>l \<in> Line. g \<union> h = l" | "g \<noteq> h \<and> \<not>(\<exists>l \<in> Line. g \<union> h = l)"
    by argo
  then show ?thesis proof (cases)
    assume "g = h" 
    from this assms have "ameasure_rel \<phi> g h = 0" by (subst coinciding_HalfLines[symmetric])
    moreover from `g = h` assms have  "ameasure_rel \<psi> g h = 0" 
      by (subst coinciding_HalfLines[symmetric])
    ultimately show ?thesis by simp
  next
    assume "\<exists>l \<in> Line. g \<union> h = l"
    from this assms have "ameasure_rel \<phi> g h = 2" by (rule_tac straight_imp_measure_pi)
    moreover from `\<exists>l \<in> Line. g \<union> h = l` assms have "ameasure_rel \<psi> g h = 2"
      by (rule_tac straight_imp_measure_pi) 
    ultimately show ?thesis by simp
  next
    assume "g \<noteq> h \<and> \<not>(\<exists>l \<in> Line. g \<union> h = l)"
    from `B \<in> Bundle` `g \<in> B` `h \<in> B`
    have "g \<in> HalfLine" "h \<in> HalfLine" "endpoint g = endpoint h"
      using brossard_bundle2b brossard_bundle2a by blast+
    from this `g \<noteq> h \<and> \<not>(\<exists>l \<in> Line. g \<union> h = l)`
    have "\<exists>!B\<in>Bundle. g \<in> B \<and> h \<in> B" using brossard_bundle1' assms(1,2,3) by presburger
    from this `B \<in> Bundle` `C \<in> Bundle` `g \<in> B` `h \<in> B` `g \<in> C` `h \<in> C`
    have "B = C" by force
    from `B \<in> Bundle` `\<phi> \<in> Acoord B` `endpoint g = endpoint h` `\<phi> \<in> Acoord B`
 `g \<in> B` `h \<in> B` `\<psi> \<in> Acoord C`
    show ?thesis
      by (subst(asm) `B = C`[symmetric], rule_tac HalfLine_measure_independence)
  qed
qed

lemma bundle_sym: "bundle g h = bundle h g"
proof-
  have comm_and:"\<forall>B.(h \<in> B \<and> g \<in> B) = (g \<in> B \<and> h \<in> B)" by blast
  have 1: "bundle g h = (SOME B. B \<in> Bundle \<and> g \<in> B \<and> h \<in> B)" by (rule bundle_def)
  from comm_and also have 2: "... = (SOME B. B \<in> Bundle \<and> h \<in> B \<and> g \<in> B)"
    by presburger
  then have 3: "... = bundle h g" using bundle_def by simp
  then show "bundle g h = bundle h g" using 1 2 3 by blast
qed

lemma halfline_bundle_measure_independence: assumes 
             "\<phi> \<in> Acoord (bundle (halfline X A) (halfline X B))" 
"\<psi> \<in> Acoord (bundle (halfline X A) (halfline X B))" 
        shows "ameasure_rel \<phi> (halfline X A) (halfline X B) = ameasure_rel \<psi> (halfline X A) (halfline X B)" 
proof -
  from assms bundle_bestdef halfline_bestdef show ?thesis 
    using HalfLine_measure_independence endpoint_agrees 
  proof -
    thm halfline_bestdef(3)
  have f1: "(halfline X A) \<in> (bundle (halfline X A) (halfline X B))"
    by (simp add: halfline_bundle_bestdef(2) endpoint_agrees halfline_bestdef(3))
  have f2: "(halfline X B) \<in> (bundle (halfline X A) (halfline X B))"
   using halfline_bundle_bestdef(2) bundle_sym endpoint_agrees halfline_bestdef(3) 
   by blast
  have "\<forall>p pa pb. bundle (halfline pa pb) (halfline pa p) \<in> Bundle"
    by (simp add: bundle_bestdef(1) endpoint_agrees halfline_bestdef(3))
  then show ?thesis
    using f2 f1 by (meson HalfLine_measure_independence assms(1) assms(2) brossard_bundle2a)
qed
qed

lemma HalfLine_bundle_measure_independence: assumes "g \<in> HalfLine" "h \<in> HalfLine"
 "endpoint g = endpoint h" 
             "\<phi> \<in> Acoord (bundle g h)" "\<psi> \<in> Acoord (bundle g h)" 
        shows "ameasure_rel \<phi> g h = ameasure_rel \<psi> g h" 
proof -
  from assms bundle_bestdef show ?thesis by (rule_tac HalfLine_measure_independence)
qed

lemma angle_at_origin: assumes"B \<in> Bundle" "\<phi> \<in> Acoord B"  "g\<in>B" "h\<in>B" 
  shows "\<exists>f\<in>B. \<phi> g - \<phi> h =4 \<phi> f" 
proof - 
  have "0 \<le> mod4(\<phi> g - \<phi> h)" "mod4(\<phi> g - \<phi> h) < 4" by (rule_tac [!] mod4_bestdef)
  from this assms have "\<exists>f \<in> B. \<phi> f = mod4(\<phi> g - \<phi> h)" using halfline_with_measure_r by blast
  then show ?thesis using eqmod4_imp_eq4 eq4_sym by blast
qed

lemma bij_at_origin: assumes"bij_betw \<phi> B {x. 0\<le>x \<and> x<4}"  "g\<in>B" "h\<in>B"
  shows "\<exists>f\<in>B. \<phi> g - \<phi> h =4 \<phi> f" 
proof - 
  have "0 \<le> mod4(\<phi> g - \<phi> h)" "mod4(\<phi> g - \<phi> h) < 4" by (rule_tac [!] mod4_bestdef)
  from this assms have "\<exists>f \<in> B. \<phi> f = mod4(\<phi> g - \<phi> h)" using nonhalfline_with_measure_r by blast
  then show ?thesis using eqmod4_imp_eq4 eq4_sym by blast
qed

definition "angle A X B = ameasure (halfline X A) (halfline X B)"

lemma angle_independence: assumes "\<phi> \<in> Acoord (bundle (halfline X A) (halfline X B))"
  shows "angle A X B = ameasure_rel \<phi> (halfline X A) (halfline X B)"
proof (subst angle_def)
  from assms show "ameasure (halfline X A) (halfline X B) = ameasure_rel \<phi> (halfline X A) (halfline X B) "
    using HalfLine_bundle_measure_independence
  

lemma bundle_halfline_bestdef: "bundle (halfline X A) (halfline X B) \<in> Bundle"
  using bundle_bestdef halfline_bestdef endpoint_agrees
  by simp

text{*  Let $\angle AOB$ be proper. If $D$ is between $A$ and $B$,
 then $0< \angle AOD < \angle AOB$.
 Conversely, if $0< \angle AOD < \angle AOB$, then the ray $OC$ meets the interval $AB$.}*}
lemma maclane: assumes "A \<noteq> B"  "A \<noteq> X" "B \<noteq> X" "between A P B" 
"\<not> (\<exists>l\<in>Line. halfline X A \<union> halfline X B = l)"
  shows "0 < angle A X P" and "angle A X P < angle A X B"
proof - 
  have bunhalf:"bundle (halfline X A) (halfline X B) \<in> Bundle" (is "?B_AB \<in> Bundle")
    by (rule bundle_halfline_bestdef)
  then obtain \<phi> where phi_def:"\<phi> \<in> Acoord (bundle (halfline X A) (halfline X B))" 
    using brossard_angle_measure1 by blast
  from assms 
  have "\<exists>C. halfline X C \<in> ?B_AB \<and>
    P \<in> halfline X C \<and>
    ameasure_rel \<phi> (halfline X A) (halfline X P) +
    ameasure_rel \<phi> (halfline X P) (halfline X B) =4
    ameasure_rel \<phi> (halfline X A) (halfline X B)"
    using brossard_continuity_halfline
    by (simp add: halfline_bundle_bestdef phi_def)
  from `between A P B` bet_imp_distinct 
  have "0 < ameasure_rel \<phi> (halfline X A) (halfline X P)"
    oops
  thm HalfLine_bundle_measure_independence
 (*angle measure axiom should give independence of angle measure*)
  thm bundle_bestdef
  thm brossard_continuity_halfline

(*Brossard says `sufficiency is obvious'.*)
lemma coord_fn_relation_mult_imp_coord: assumes "B \<in> Bundle" "\<phi> \<in> Acoord B" 
"bij_betw \<psi> B {x. 0\<le>x \<and> x<4}"
"\<exists>\<theta> \<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> (\<forall>h\<in>B. \<psi> h = \<epsilon>*\<phi> h + \<theta>)"
shows "\<psi> \<in> Acoord B"
proof-
  from assms have angle_measure3:"\<psi> \<in> Acoord B \<equiv> \<forall>g\<in>B. \<forall>h\<in>B. \<bar>\<phi> g - \<phi> h\<bar> =4 \<bar>\<psi> g - \<psi> h\<bar>"
    by (rule_tac brossard_angle_measure3)
  have "\<forall>g\<in>B. \<forall>h\<in>B. \<bar>\<phi> g - \<phi> h\<bar> =4 \<bar>\<psi> g - \<psi> h\<bar>"
  proof (intro ballI)
    fix g h assume "g\<in>B" "h\<in>B"
    from assms(4) obtain \<theta> \<epsilon> where "\<bar>\<epsilon>\<bar>=1" "\<forall>h\<in>B. \<psi> h = \<epsilon>*\<phi> h + \<theta>" by blast
    from `g\<in>B` `h\<in>B` this have psi_def:"\<psi> h = \<epsilon>*\<phi> h + \<theta>" "\<psi> g = \<epsilon>*\<phi> g + \<theta>" by blast+
    from `\<bar>\<epsilon>\<bar>=1` consider "\<epsilon>=1" | "\<epsilon>=-1" by linarith
    then have "\<bar>\<phi> g - \<phi> h\<bar> = \<bar>\<epsilon>*\<phi> g - \<epsilon>*\<phi> h\<bar>" 
    proof (cases)
      assume "\<epsilon>=1"
      then show "\<bar>\<phi> g - \<phi> h\<bar> = \<bar>\<epsilon>*\<phi> g - \<epsilon>*\<phi> h\<bar>" by simp
    next
      assume "\<epsilon>=-1"
      then show "\<bar>\<phi> g - \<phi> h\<bar> = \<bar>\<epsilon>*\<phi> g - \<epsilon>*\<phi> h\<bar>" by simp
    qed
    from this psi_def have "\<bar>\<phi> g - \<phi> h\<bar> = \<bar>\<psi> g - \<psi> h\<bar>" by force
    then show "\<bar>\<phi> g - \<phi> h\<bar> =4 \<bar>\<psi> g - \<psi> h\<bar>" using eq4_refl by simp
  qed
  from this angle_measure3 show "\<psi> \<in> Acoord B" by simp
qed

definition phi::"'p \<Rightarrow> 'p \<Rightarrow> real \<Rightarrow> real" where
 "phi X A d = ameasure (halfline X A) (halfline X (inv (\<lambda>P. distance A P) d))"
thm between_imp_collinear
lemma assumes "between A P Q" "distance A P = distance A Q"
  shows "P = Q"
proof -
  thm between_def
  from line_bestdef have "P \<in> line A P"
    by simp
  from `between A P Q` have "Q \<in> line A P" by (rule between_imp_collinear)
  obtain x where x_def:"x \<in> Coord (line A P)"
    using distance_expanded_def by blast
  from this `P \<in> line A P` have 1:"distance A P = \<bar>x A - x P\<bar>"
    by (rule point_on_line_consistent_coordfn)
  from x_def `Q \<in> line A P` have 2:"distance A Q = \<bar>x A - x Q\<bar>"
    by (rule point_on_line_consistent_coordfn)
  from 1 2 `distance A P = distance A Q` have "\<bar>x A - x P\<bar> = \<bar>x A - x Q\<bar>"
    by simp  
  from x_def `between A P Q` `Q \<in> line A P` 
  have "x A < x P \<and> x P < x Q \<or> x Q < x P \<and> x P < x A"
    using between_expanded_def by auto

lemma assumes "P \<in> halfline A B" "Q \<in> halfline A B" "distance A P = distance A Q"
  shows "P = Q"
proof -
  from `P \<in> halfline A B` have "P \<in> line A B"
    using halfline_propersubset by blast
  from `Q \<in> halfline A B` have "Q \<in> line A B"
    using halfline_propersubset by blast
  obtain x where x_def:"x \<in> Coord (line A B)"
    using distance_expanded_def by blast
  from this `P \<in> line A B` have 1:"distance A P = \<bar>x A - x P\<bar>"
    by (rule point_on_line_consistent_coordfn)
  from x_def `Q \<in> line A B` have 2:"distance A Q = \<bar>x A - x Q\<bar>"
    by (rule point_on_line_consistent_coordfn)
  from 1 2 `distance A P = distance A Q` have "\<bar>x A - x P\<bar> = \<bar>x A - x Q\<bar>"
    by simp
  then consider "x P = x Q" | "x P = - x Q"

lemma "bij_betw (\<lambda>P. distance A P) {P. P \<in> halfline A B \<and> P\<noteq>A} {x. 0<x}" thm distance_rel_def
proof (subst bij_betw_def, rule conjI)
  show "inj_on (distance A) {P. P \<in> halfline A B  \<and> P\<noteq>A}"
  proof (subst inj_on_def, safe)
    fix x y assume "x \<in> halfline A B" "y \<in> halfline A B" 
    "x \<noteq> A" "y \<noteq> A" "distance A x = distance A y" 
    
    thm distance_def
lemma "bij_betw (\<lambda>d. phi X A d) {x. 0 < x} {x. 0\<le>x \<and> x<4}" 
proof (subst bij_betw_def, rule conjI)
  show "inj_on (phi X A) (Collect ((<) 0))"
  proof (subst inj_on_def, safe)
    fix x y assume "0 < x" "0 < y" "phi X A x = phi X A y"
    then have "ameasure (halfline X A) (halfline X (inv (\<lambda>P. distance A P) x))
             = ameasure (halfline X A) (halfline X (inv (\<lambda>P. distance A P) y))"
      by ((subst(asm) phi_def),(subst(asm) phi_def))
    then have "(halfline X (inv (\<lambda>P. distance A P) x)) = 
               (halfline X (inv (\<lambda>P. distance A P) y))"
    
    
    
  oops
lemma mono_phi: "mono_on (phi X A) {x. 0 < x \<and> x < 4}" (is "mono_on (phi X A) ?ab")
  oops

(*H is any positive real so H can be Huge*)
lemma  assumes mono:"mono_on (phi X A) {x. 0 < x \<and> x < 4}" (is "mono_on (phi X A) ?ab")
  and bij:"bij_betw (phi X A) {x. 0 < x} {x. 0 < x \<and> x < 4}" 
shows "\<forall>x \<in> {x. (a::real) < x \<and> x < b}. (isCont (phi X A) x)"

  


lemma weak_imp_strong_quantifier_swap: assumes "\<forall>l\<in>L. \<exists>\<epsilon>\<in>E. P \<epsilon> l" 
"\<forall>\<epsilon>1\<in>E. \<forall>\<epsilon>2\<in>E. \<forall>l1\<in>L. \<forall>l2\<in>L. P \<epsilon>1 l1 \<and> P \<epsilon>2 l2 \<longrightarrow> \<epsilon>1 = \<epsilon>2" "\<exists>\<epsilon>. \<epsilon>\<in>E"
  shows "\<exists>\<epsilon>\<in>E. \<forall>l\<in>L. P \<epsilon> l"
proof (cases "\<exists>l. l\<in>L")
  case True
  then obtain l where "l\<in>L" by blast
  from this assms(1) obtain \<epsilon> where "\<epsilon>\<in>E" "P \<epsilon> l" by blast
  from this assms(2) have "\<forall>l\<in>L. P \<epsilon> l" 
    using \<open>l \<in> L\<close> assms(1) by blast
  from this `\<epsilon>\<in>E` show ?thesis by blast
next
  case False
  from this assms(3) show ?thesis by blast
qed


lemma coord_fn_relation_coord_imp_mult: assumes "\<phi> \<in> Acoord B" "\<psi> \<in> Acoord B" "B \<in> Bundle"
  shows "\<exists>\<theta> \<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> (\<forall>h\<in>B. \<psi> h = \<epsilon>*\<phi> h + \<theta>)"
(* "\<exists>\<theta>. \<forall>h\<in>B. \<bar>\<psi> h\<bar> = \<bar>\<phi> h\<bar> + \<theta>" may be the same but it's not obvious, thus it should be proven, so
it's more work than it's worth. Furthermore, it may not be the most useful formalisation.*)
proof -
  have "0 \<le> (0::real) \<and> (0::real) < 4" by simp
  from `B \<in> Bundle` `\<phi> \<in> Acoord B` `0 \<le> (0::real) \<and> (0::real) < 4`
  have "\<exists>!h. h \<in> B \<and> \<phi> h = 0" by (rule_tac halfline_with_measure_r)
  then obtain h where "h \<in> B" and "\<phi> h = 0" by blast
  have "0 \<le> (2::real) \<and> (2::real) < 4" by simp
  from `B \<in> Bundle` `\<phi> \<in> Acoord B` `0 \<le> (2::real) \<and> (2::real) < 4`
  have "\<exists>!h. h \<in> B \<and> \<phi> h = 2" by (rule_tac halfline_with_measure_r)
  then obtain g where "g \<in> B" and "\<phi> g = 2" by blast
  from `h \<in> B` `g \<in> B` assms have "\<bar>\<psi> g - \<psi> h\<bar> =4 \<bar>\<phi> g - \<phi> h\<bar>" (*how do we get equality?*)
    by (rule_tac brossard_angle_measure_2_3)
  also have "... =4 \<bar>2\<bar>" using `\<phi> h = 0` `\<phi> g = 2` mod4_eq4 by auto
  finally have "\<bar>\<psi> g - \<psi> h\<bar> =4 2" by simp
  then have "\<psi> g - \<psi> h =4 2" 
  proof (cases "\<psi> g - \<psi> h \<ge> 0")
    assume "\<psi> g - \<psi> h \<ge> 0"
    then show "\<psi> g - \<psi> h =4 2" using `\<bar>\<psi> g - \<psi> h\<bar> =4 2` eq4_refl by simp
  next
    assume "\<not>(\<psi> g - \<psi> h \<ge> 0)"
    then have "-(\<psi> g - \<psi> h) =4 2" using `\<bar>\<psi> g - \<psi> h\<bar> =4 2` eq4_refl by simp
    then have "(\<psi> g - \<psi> h) =4 -2" using eq4_neg_eq
      by fastforce
    then show "\<psi> g - \<psi> h =4 2" using eq4_2_inv by (rule eq4_trans)
  qed
  then have "\<psi> g =4 2 + \<psi> h" by (subst(asm) eq4_swap)
(*So \<psi> h is our \<theta>. h is m. *)
  have weak_quantifier_order:"\<forall>l\<in>B.\<exists>\<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> \<psi> l =4 \<epsilon> *\<phi> l + \<psi> h"
  proof
    fix l assume "l \<in> B"
    from `h \<in> B` `l \<in> B` assms have "\<bar>\<psi> l - \<psi> h\<bar> =4 \<bar>\<phi> l - \<phi> h\<bar>" 
      by (rule_tac brossard_angle_measure_2_3)
    from this `\<phi> h = 0` have hl1:"\<bar>\<psi> l - \<psi> h\<bar> =4 \<bar>\<phi> l\<bar>" by simp
    show "\<exists>\<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> \<psi> l =4 \<epsilon> *\<phi> l + \<psi> h"
    proof (cases "(\<psi> l - \<psi> h) < 0")
      case True
      from this hl1 have hl2:"-(\<psi> l - \<psi> h) =4 \<bar>\<phi> l\<bar>" using abs_real_def
        by fastforce
      show "\<exists>\<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> \<psi> l =4 \<epsilon> *\<phi> l + \<psi> h"
      proof (cases "\<phi> l < 0")
        case True
        from this hl2 have "-(\<psi> l - \<psi> h) =4 -\<phi> l" using abs_real_def
          by fastforce
        then have "\<psi> l =4 \<phi> l + \<psi> h" using eq4_neg_eq eq4_swap by blast
        then have "\<psi> l =4 1*\<phi> l + \<psi> h" by simp
        moreover have "\<bar>(1::real)\<bar>=1" using abs_real_def by fastforce
        ultimately show "\<exists>\<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> \<psi> l =4 \<epsilon> *\<phi> l + \<psi> h" by blast
      next
        case False
        from this hl2 have "\<psi> h - \<psi> l =4 \<phi> l" using abs_real_def
          by fastforce
        then have "- \<psi> l =4 \<phi> l - \<psi> h" using eq4_swap by fastforce
        then have "- \<psi> l =4 -1*-1*\<phi> l - \<psi> h" by simp
        then have "\<psi> l =4 -1*\<phi> l + \<psi> h" using eq4_neg_eq by fastforce
        moreover have "\<bar>(-1::real)\<bar>=1" using abs_real_def by fastforce
        ultimately show "\<exists>\<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> \<psi> l =4 \<epsilon> *\<phi> l + \<psi> h" by blast
      qed
    next
      case False
      from this hl1 have hl2:"\<psi> l - \<psi> h =4 \<bar>\<phi> l\<bar>" using abs_real_def
        by fastforce
      show "\<exists>\<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> \<psi> l =4 \<epsilon> *\<phi> l + \<psi> h"
      proof (cases "\<phi> l < 0")
        case True
        from this hl2 have "\<psi> l - \<psi> h =4 -\<phi> l" using abs_real_def
          by fastforce
        then have "\<psi> l =4 - \<phi> l + \<psi> h" by (subst(asm) eq4_swap(2))
        then have "\<psi> l =4 -1*\<phi> l + \<psi> h" by simp
        moreover have "\<bar>(-1::real)\<bar>=1" using abs_real_def by fastforce
        ultimately show "\<exists>\<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> \<psi> l =4 \<epsilon> *\<phi> l + \<psi> h" by blast
      next
        case False
        from this hl2 have "-(\<psi> h - \<psi> l) =4 \<phi> l" using abs_real_def
          by fastforce
        then have "-(\<psi> h - \<psi> l) =4 -1*-1*\<phi> l" by simp
        then have "\<psi> h - \<psi> l =4 - \<phi> l" using eq4_neg_eq by fastforce
        then have "\<psi> l =4 \<phi> l + \<psi> h" using eq4_neg_eq eq4_swap by fastforce
        then have "\<psi> l =4 1*\<phi> l + \<psi> h" by simp
        moreover have "\<bar>(1::real)\<bar>=1" using abs_real_def by fastforce
        ultimately show "\<exists>\<epsilon>.\<bar>\<epsilon>\<bar>=1 \<and> \<psi> l =4 \<epsilon> *\<phi> l + \<psi> h" by blast
      qed
    qed
  qed
  define E where "E = {\<epsilon>. \<bar>\<epsilon>\<bar>=(1::real)}"
  have "\<exists>\<epsilon>\<in>E. \<forall>l\<in>B. (\<psi> l = \<epsilon>*\<phi> l + \<psi> h)"
  proof (rule weak_imp_strong_quantifier_swap)
    show "\<exists>\<epsilon>. \<epsilon> \<in> E" using E_def abs_real_def by fastforce
    show "\<forall>\<epsilon>1\<in>E. \<forall>\<epsilon>2\<in>E. \<forall>l1\<in>B. \<forall>l2\<in>B. \<psi> l1 = \<epsilon>1 * \<phi> l1 + \<psi> h \<and> \<psi> l2 = \<epsilon>2 * \<phi> l2 + \<psi> h \<longrightarrow> \<epsilon>1 = \<epsilon>2"
    proof (intro ballI, rule impI, erule conjE)
      fix \<epsilon>1 \<epsilon>2 l1 l2 
      assume "\<epsilon>1 \<in> E" "\<epsilon>2 \<in> E" "l1 \<in> B" "l2 \<in> B"
      "\<psi> l1 = \<epsilon>1 * \<phi> l1 + \<psi> h" "\<psi> l2 = \<epsilon>2 * \<phi> l2 + \<psi> h"
      show "\<epsilon>1 = \<epsilon>2"
      proof (cases "\<epsilon>1 = 1")
        case True
        show "\<epsilon>1 = \<epsilon>2"
        proof (cases "\<epsilon>2 = 1")      
          case True 
          show "\<epsilon>1 = \<epsilon>2" using `\<epsilon>1 = 1` `\<epsilon>2 = 1` by simp
        next
          case False
          from this E_def abs_real_def have "\<epsilon>2 = -1" 

    from weak_quantifier_order show "\<forall>l\<in>B. \<exists>\<epsilon>\<in>E. \<psi> l = \<epsilon> * \<phi> l + \<psi> h" using E_def

lemma coord_fn_relation: assumes "\<phi> \<in> Acoord B" "bij_betw \<psi> B {x. 0\<le>x \<and> x<4}" "B \<in> Bundle"
  shows "\<psi> \<in> Acoord B = (\<exists>\<theta>. \<forall>h\<in>B. \<bar>\<psi> h\<bar> = \<bar>\<phi> h\<bar> + \<theta>)"
  oops

definition "Triangles = {T. \<exists> P Q R. P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P \<and> T = {P,Q,(R::'p)}}"

definition "P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P \<Longrightarrow> triangle P Q R = {P,Q,(R::'p)}"

definition "T \<in> Triangles \<Longrightarrow> isProper T = (\<exists>P Q R. \<not> (collinear P Q R) \<and> T = {P,Q,(R::'p)})"

(*definition "proper_triangle P Q R = (SOME T. "*)

definition "\<not> (collinear P Q R) \<Longrightarrow> P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P \<Longrightarrow> proper_triangle P Q R = triangle P Q R"

lemma distinct_imp_tri:assumes "P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P" shows "(triangle P Q R) \<in> Triangles"
proof -
  from assms have "triangle P Q R = {P,Q,R}" by (rule triangle_def)
  show "(triangle P Q R) \<in> Triangles" using Triangles_def `triangle P Q R = {P,Q,R}` assms
    by auto
qed 

lemma tri_sym: assumes "P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P" shows "(triangle P Q R) = (triangle Q R P)"
"(triangle P Q R) = (triangle R P Q)" "(triangle P Q R) = (triangle R Q P)"
"(triangle P Q R) = (triangle P R Q)" "(triangle P Q R) = (triangle Q P R)"
  using assms insert_commute triangle_def by auto


(*lemma assumes "\<not> (collinear P Q R)" "P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P" shows "(proper_triangle P Q R) \<in> Triangles"
proof -
  from assms(2) have "(triangle P Q R) \<in> Triangles" by (rule distinct_imp_tri)
  
    
    show "(proper_triangle P Q R) \<in> Triangles"*)
thm isProper_def
lemma assumes "P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P" "isProper (triangle P Q R)" 
  shows "\<not> (collinear P Q R)"
proof -
  from `P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P` have "(triangle P Q R) \<in> Triangles" by (rule distinct_imp_tri)
  from this have 
  isprop_PQR:"isProper (triangle P Q R) = (\<exists>P1 Q1 R1. \<not> collinear P1 Q1 R1 \<and> (triangle P Q R) = {P1, Q1, R1})"
    by (rule_tac isProper_def)
  from `isProper (triangle P Q R)`
  have somePQR:"(\<exists>P1 Q1 R1. \<not> collinear P1 Q1 R1 \<and> (triangle P Q R) = {P1, Q1, R1})"
    by (subst(asm) isprop_PQR)
  from somePQR  obtain P1 Q1 R1 where P1Q1R1_def:"\<not> collinear P1 Q1 R1 \<and> (triangle P Q R) = {P1, Q1, R1}"
    by blast
  from `P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P` have "triangle P Q R = {P,Q,R}" by (rule triangle_def)
  from P1Q1R1_def have "P1\<noteq>Q1 \<and> Q1\<noteq>R1 \<and> R1\<noteq>P1"
    using noncollinear_imp_dist by auto
  have "triangle P1 Q1 R1 = {P1, Q1, R1}" by triangle_def
  from this P1Q1R1_def `P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P` tri_sym have "triangle P Q R = triangle P1 Q1 R1"
  from this P1Q1R1_def show 
  thm isProper_def
definition "side P Q T = (P \<noteq> Q \<and> P \<in> T \<and> Q \<in> T)" 

definition t_angle where "P\<noteq>Q \<and> Q\<noteq>R \<and> R\<noteq>P \<Longrightarrow>
 t_angle Q P R = ameasure (halfline P Q) (halfline P R)" 
(*prove something about the pair of halflines themselves*)

definition "T \<in> Triangles \<Longrightarrow> S \<in> Triangles \<Longrightarrow> similar T S = 
(\<exists> A B C P Q R. triangle P Q R = T \<and> triangle A B C = S \<and> 
distance P Q / distance A B = distance Q R / distance B C \<and>
distance Q R / distance B C = distance R P / distance C A \<and>
t_angle R P Q = t_angle C A B \<and> t_angle P Q R = t_angle A B C \<and> t_angle Q R P = t_angle B C A)" 
end


locale Triangles = Continuity isBundle
  for isBundle :: "'p set set \<Rightarrow> bool"  +
  assumes brossard_similarity: "\<lbrakk>triangle A B C  \<in> Triangles; triangle P Q R \<in> Triangles; 
distance P Q / distance A B = distance Q R / distance B C; t_angle P Q R = t_angle A B C\<rbrakk> 
\<Longrightarrow> similar (triangle A B C) (triangle P Q R)"
context Triangles
begin

lemma brossard_similarity: assumes "triangle A B C  \<in> Triangles" "triangle P Q R \<in> Triangles"
"t_angle R P Q = t_angle C A B \<and> t_angle P Q R = t_angle A B C" "isProper (triangle A B C)"
"isProper (triangle P Q R)"
shows "similar (triangle A B C) (triangle P Q R)"
proof -
  from `isProper (triangle A B C)` have "\<not> (collinear A B C)"
    thm isProper_def
  have "distance A B > 0"
  



end




end