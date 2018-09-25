theory Brossard_Geometry imports Main Real All_True_or_All_False Mod4

begin

locale Lines =
  fixes isLine :: "'p set \<Rightarrow> bool"
  assumes 
  brossard_line1: "\<exists> (A::'p) B. A \<noteq> B"
  and point_line_brossard_line2: "A \<noteq> B \<Longrightarrow> \<exists>! l. isLine l \<and> A \<in> l \<and> B \<in> l" 
  and brossard_line3: "\<exists> A B C. \<not>(\<exists> l. isLine l \<and> A \<in> l \<and> B \<in> l \<and> C \<in> l)" 

context Lines
begin

definition "Line = {l. isLine l}"

lemma point_line_brossard_line2': "A \<noteq> B \<Longrightarrow> \<exists>! l\<in> Line. A \<in> l \<and> B \<in> l"
  using point_line_brossard_line2 Line_def by auto

lemma brossard_line3': "\<exists> A B C. \<not>(\<exists> l \<in> Line. A \<in> l \<and> B \<in> l \<and> C \<in> l)"
  using brossard_line3 Line_def by auto

lemma second_point: "\<exists> B. (A::'p) \<noteq> B"
  by (metis brossard_line1)

lemma point_not_on_line: assumes "l \<in> Line" shows "\<exists>B. \<not>(B \<in> l)" 
proof (rule ccontr)
  assume "\<not> (\<exists>B. B \<notin> l)" (*every point is on the line*)
  from brossard_line3' obtain A B C where ABC_def:  "\<not>(\<exists> l \<in> Line. A \<in> l \<and> B \<in> l \<and> C \<in> l)"
    by blast
  from `\<not> (\<exists>B. B \<notin> l)` have "A \<in> l \<and> B \<in> l \<and> C \<in> l" by blast
  from this assms ABC_def show False by blast
qed

lemma line_through_point: "\<exists> l \<in> Line. (A::'p) \<in> l"
proof -
 have  "\<exists> l. isLine l \<and> (A::'p) \<in> l" by (metis second_point point_line_brossard_line2)
 then show ?thesis using Line_def by simp
qed

definition "line A B == (SOME l. isLine l \<and> A \<in> l \<and> B \<in> l)"

(*lemma old_line_def: "line A B == (if A \<noteq> B then THE l. isLine l \<and> A \<in> l \<and> B \<in> l 
                     else SOME l. isLine l \<and> A \<in> l)"
  using line_def point_line_brossard_line2 *)

lemma unique_line: assumes "A \<noteq> B"  shows "isLine (line A B)"
                         and "A \<in> (line A B)" and "B \<in> (line A B)"
proof -
  have new_line_def:  "line A B = (SOME l. isLine l \<and> A \<in> l \<and> B \<in> l)" by (simp add: line_def)
  from `A \<noteq> B` have "\<exists>!l. isLine l \<and> A \<in> l \<and> B \<in> l" by (rule point_line_brossard_line2)
  then have "\<exists>l. isLine l \<and> A \<in> l \<and> B \<in> l" by auto
  then have "isLine (line A B) \<and> A \<in> (line A B) \<and> B \<in> (line A B)"
    by (subst new_line_def,subst new_line_def,subst new_line_def, rule someI_ex)
  then show "isLine (line A B)" and "A \<in> (line A B)" and "B \<in> (line A B)" by auto 
qed

lemma line_sym: "line A B = line B A"
proof (cases "A = B")
  assume "A = B" then show "line A B = line B A" by simp
next
  assume "A \<noteq> B" then have "\<exists>!l. isLine l \<and> A \<in> l \<and> B \<in> l" by (rule point_line_brossard_line2)
  moreover from `A \<noteq> B` unique_line have "isLine (line A B) \<and> A \<in> line A B \<and> B \<in> line A B"
    by presburger
  moreover from `A \<noteq> B` unique_line have "isLine (line B A) \<and> A \<in> line B A \<and> B \<in> line B A"
    by presburger
  ultimately show "line A B = line B A" by blast
qed

lemma line_bestdef:    shows "(line A B) \<in> Line"
                         and "A \<in> (line A B)" and "B \<in> (line A B)"
proof (case_tac [!] "A = B")
  assume "A \<noteq> B"
  then show "(line A B) \<in> Line" and "A \<in> (line A B)" and "B \<in> (line A B)"
    using unique_line Line_def by auto
next
  assume "A = B"
    have new_line_def:  "line A B = (SOME l. isLine l \<and> A \<in> l)" by (simp add: line_def `A = B`)
    obtain C where "C\<noteq>A" using second_point by fastforce
    then have "isLine (line A C) \<and> A \<in> (line A C)" by (auto simp: unique_line)
    then have "\<exists> l. isLine l \<and> A \<in> l" by auto
    then have "isLine (line A B) \<and> A \<in> (line A B)"
      by (subst new_line_def, subst new_line_def, rule someI_ex)
    then have "isLine (line A B)"  and "A \<in> (line A B)" by auto
    then show "(line A B) \<in> Line"  and "A \<in> (line A B)" using Line_def by auto
    then show "B \<in> (line A B)" using `A = B`  by auto
  qed

lemma line_bestdef_inv: assumes "l \<in> Line" and "A \<in> l" and "B \<in> l" and  "A\<noteq>B"
                          shows "l = (line A B)" 
proof -
  from `A\<noteq>B` have "\<exists>!l \<in> Line. A \<in> l \<and> B \<in> l" by (rule point_line_brossard_line2')
  moreover have "(line A B) \<in> Line \<and> A \<in> (line A B) \<and> B \<in> (line A B)" by (simp only: line_bestdef)
  moreover have "l \<in> Line\<and> A \<in> l\<and> B \<in> l" by (simp only: assms(1,2,3))
  ultimately show ?thesis by blast
qed

lemma not_on_line_sym: assumes "A\<noteq>B" "C \<notin> line A B" shows "A \<notin> line B C"
(*equivalent to symmetry of collinearity (basically says 'ABC noncollinear iff BCA noncollinear)
 which follows from collinear_bestdef*)
proof 
  assume "A \<in> line B C"
  have "line B C \<in> Line" "B \<in> line B C"  by (rule_tac [!] line_bestdef)
  from `line B C \<in> Line` `A \<in> line B C` `B \<in> line B C` assms(1) have "line B C = line A B"
    by (rule line_bestdef_inv)
  have "C \<in> line A B" by (subst `line B C = line A B`[symmetric], rule line_bestdef)
  from this assms(2) show False by simp
qed

lemma  assumes "A\<noteq>B" "A \<in> line B C"  shows on_line_sym:"C \<in> line A B" 
and same_line:"line B C = line A B"
proof -
  have "line B C \<in> Line" "B \<in> line B C"  by (rule_tac [!] line_bestdef)
  from `line B C \<in> Line` `A \<in> line B C` `B \<in> line B C` assms(1) show "line B C = line A B"
    by (rule line_bestdef_inv)
  show "C \<in> line A B" by (subst `line B C = line A B`[symmetric], rule line_bestdef)
qed

lemma line_independence:  assumes "A\<noteq>B" "A \<in> line B C" shows "line B C = line A B" 
"line C B = line A B" "line C B = line B A" "line B C = line B A"
proof -
  from assms show "line B C = line A B" by (rule same_line)
  then show "line C B = line A B" by (subst line_sym)
  then show "line C B = line B A" by (subst line_sym)
  then show "line B C = line B A" by (subst line_sym)
qed
  
definition "collinear A B C = (C \<in> line A B \<or> A = B)" 

lemma collinear_bestdef1: "collinear A B C \<Longrightarrow> \<exists>l \<in> Line. A \<in> l\<and> B \<in> l\<and>C\<in>l"
  and collinear_bestdef2: "\<exists>l \<in> Line. A \<in> l\<and> B \<in> l\<and>C\<in>l \<Longrightarrow> collinear A B C"
proof -
  assume "collinear A B C"
  show "\<exists>l \<in> Line. A \<in> l\<and> B \<in> l\<and>C\<in>l"
  proof (cases "A=B")
    assume "A=B"
    then have "(line A C) \<in> Line\<and> A \<in> (line A C)\<and> B \<in> (line A C)\<and>C\<in>(line A C)"
      by (simp add: line_bestdef)
    then show ?thesis by blast
  next
    assume "A \<noteq> B"
    from this `collinear A B C` collinear_def have "C\<in>(line A B)" by simp
    then show ?thesis using line_bestdef by fast
  qed
next
  assume l_def:"\<exists>l \<in> Line. A \<in> l\<and> B \<in> l\<and>C\<in>l"
  show "collinear A B C"
  proof (cases "A=B")
    assume "A=B"
    then show ?thesis using collinear_def by simp
  next
    assume "A\<noteq>B"
    from this l_def show ?thesis using line_bestdef_inv collinear_def by blast
  qed
qed


lemma collinear_sym: assumes "collinear P Q R" shows "(collinear Q R P)"
"(collinear R P Q)" "(collinear R Q P)"
"(collinear P R Q)" "(collinear Q P R)"
proof -
  from assms have "\<exists>l\<in>Line. P \<in> l \<and> Q \<in> l \<and> R \<in> l" by (rule collinear_bestdef1)
  then have "\<exists>l\<in>Line. Q \<in> l \<and> R \<in> l \<and> P \<in> l" "\<exists>l\<in>Line. R \<in> l \<and> P \<in> l \<and> Q \<in> l"
  "\<exists>l\<in>Line. R \<in> l \<and> Q \<in> l \<and> P \<in> l" "\<exists>l\<in>Line. P \<in> l \<and> R \<in> l \<and> Q \<in> l" 
  "\<exists>l\<in>Line. Q \<in> l \<and> P \<in> l \<and> R \<in> l"
    by blast+
  from this show "(collinear Q R P)" "(collinear R P Q)" "(collinear R Q P)"
  "(collinear P R Q)" "(collinear Q P R)"
    using collinear_bestdef2 by auto
qed

end

locale Line_Measure = Lines isLine
  for isLine ::"'p set \<Rightarrow> bool" +
  fixes Coord  :: "'p set \<Rightarrow> ('p \<Rightarrow> real) set" 
  assumes
  brossard_line_measure1: "l \<in> Line \<Longrightarrow> \<exists> x. x \<in> Coord l" 
  and brossard_line_measure2: "\<lbrakk>l \<in> Line; x \<in> Coord l\<rbrakk> \<Longrightarrow> bij_betw x l (UNIV::real set)"
  and brossard_line_measure3: "l \<in> Line \<Longrightarrow> \<lbrakk>x_i \<in> Coord l ; bij_betw x_j l (UNIV::real set)\<rbrakk> 
 \<Longrightarrow> ((x_j \<in> Coord l) =  (\<forall> A \<in> l. \<forall> B \<in> l. \<bar>x_i A - x_i B\<bar> = \<bar>x_j A - x_j B\<bar> ))"

context Line_Measure
begin

lemma two_points_on_line: assumes "l \<in> Line" shows "\<exists> A \<in> l. \<exists> B \<in> l.  A \<noteq> B"
proof -
  obtain x where "x \<in> Coord l" by (rule exE, rule brossard_line_measure1, rule `l \<in> Line`)
  from `l \<in> Line` this have "bij_betw x l (UNIV::real set)" by (rule brossard_line_measure2)
  from `bij_betw x l UNIV` have "x ` l = (UNIV::real set)" 
    by (subst(asm) bij_betw_def, rule_tac conjunct2)
  from this have "{y. \<exists>z\<in>l. y = x z} = UNIV" by (subst(asm) image_def)
  from this obtain B where "B \<in> l" and "1 = x B" by blast
  from `{y. \<exists>z\<in>l. y = x z} = UNIV` obtain A where "A \<in> l" and "2 = x A" by blast
  have "1\<noteq>(2::real)" by simp
  from this `1 = x B`  `2 = x A` have "A \<noteq> B" by force
  from this `A \<in> l` `B \<in> l` show ?thesis by blast
qed

lemma coordfn_preserves_distinctness: 
      assumes "l \<in> Line" and  "x\<in> Coord l" and "A \<in> l" and "B \<in> l"
      shows "(A=B) =(x A = x B)"
proof (rule iffI,erule arg_cong, rule ccontr)
  assume "x A = x B"
  assume "A \<noteq> B"
  from assms(1,2) have "bij_betw x l (UNIV::real set)" by (rule brossard_line_measure2)
  then have "inj_on x l" using bij_betw_def by blast
  then have "(\<forall>z\<in>l. \<forall>y\<in>l. x z = x y \<longrightarrow> z = y)" by (subst inj_on_def[symmetric])
  from this `x A = x B` assms(3,4) have "A=B" by fast
  from this `A \<noteq> B` show False by safe
qed

lemma brossard_line_measure_2_3: assumes "l \<in> Line"  " x_i \<in> Coord l" "x_j \<in> Coord l" "A\<in>l" "B\<in>l"
shows "\<bar>x_i A - x_i B\<bar> = \<bar>x_j A - x_j B\<bar>"
proof -
  from assms(1,3) have "bij_betw x_j l (UNIV::real set)" by (rule brossard_line_measure2)
  from assms(1,2) this have
 "((x_j \<in> Coord l) =  (\<forall> A \<in> l. \<forall> B \<in> l. \<bar>x_i A - x_i B\<bar> = \<bar>x_j A - x_j B\<bar>))" 
    by (rule brossard_line_measure3) 
  from assms(3,4,5) this show ?thesis by fast
qed

definition "x \<in> Coord (line A B) \<Longrightarrow> distance_rel x A B == \<bar>x A - x B\<bar>"

definition "between_rel == \<lambda>x A B C.(if (C \<in> (line A B) \<and> x \<in> Coord (line A B)) 
                                     then (x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A)
                                     else False)"

lemma bet_imp_distinct_rel: assumes "between_rel x A B C"
        shows "A \<noteq> B" and "B \<noteq> C" and "A \<noteq> C"
proof -
  from assms between_rel_def have "(x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A)" by meson
  from this show "A \<noteq> B" and "B \<noteq> C" and "A \<noteq> C" by auto
qed

lemma betweenness_independence:
shows "\<exists>between. \<forall>x \<in> (Coord (line A B)). between = between_rel x A B C"
proof (cases "C \<in> (line A B)")
  case False
  from this between_rel_def have "\<forall>x. (False = between_rel x A B C)" by presburger
  then show "\<exists>between. \<forall>x\<in>Coord (line A B). between = between_rel x A B C" by meson
next
  case True
  have "(line A B) \<in> Line" using line_bestdef by auto
  then obtain x_i where x_i_def:"x_i \<in> Coord (line A B)" using brossard_line_measure1 by auto
  show "\<exists>between. \<forall>x\<in>Coord (line A B). between = between_rel x A B C"
  proof (rule exI,rule ballI)
    fix x_j 
    assume "x_j \<in> Coord (line A B)"
    from `(line A B) \<in> Line` this have "bij_betw x_j (line A B) (UNIV::real set)" 
      by (rule brossard_line_measure2)
    from `(line A B) \<in> Line` x_i_def this
    have "(x_j \<in> Coord (line A B)) 
= (\<forall>X\<in>(line A B). \<forall>Y\<in>(line A B). \<bar>x_i X - x_i Y\<bar> = \<bar>x_j X - x_j Y\<bar>)"
      by (rule brossard_line_measure3)
    from this `x_j \<in> Coord (line A B)`
    have rel_distance:"\<forall>X\<in>(line A B). \<forall>Y\<in>(line A B). \<bar>x_i X - x_i Y\<bar> = \<bar>x_j X - x_j Y\<bar>"
      by simp
    have "A \<in> (line A B)" and "B \<in> (line A B)" by (rule line_bestdef,rule line_bestdef)
    from this `C \<in> (line A B)` rel_distance have "\<bar>x_i A - x_i B\<bar> = \<bar>x_j B - x_j A\<bar>"
                                             and "\<bar>x_i A - x_i C\<bar> = \<bar>x_j C - x_j A\<bar>"
                                             and "\<bar>x_i B - x_i C\<bar> = \<bar>x_j C - x_j B\<bar>" by (simp_all)
    consider "\<bar>x_i A - x_i B\<bar> = 0 \<or> \<bar>x_i B - x_i C\<bar> = 0 \<or> \<bar>x_i A - x_i C\<bar> = 0" |
             "\<bar>x_i A - x_i B\<bar> \<noteq> 0 \<and> \<bar>x_i B - x_i C\<bar> \<noteq> 0 \<and> \<bar>x_i A - x_i C\<bar> \<noteq> 0"
      by linarith
    then show "between_rel x_i A B C = between_rel x_j A B C"
    proof (cases)
      assume "\<bar>x_i A - x_i B\<bar> \<noteq> 0 \<and> \<bar>x_i B - x_i C\<bar> \<noteq> 0 \<and> \<bar>x_i A - x_i C\<bar> \<noteq> 0"
      then have "\<bar>x_i A - x_i B\<bar> \<noteq> 0" and "\<bar>x_i B - x_i C\<bar> \<noteq> 0" and "\<bar>x_i A - x_i C\<bar> \<noteq> 0" 
        by (simp_all)
       define P where "P = (\<lambda>X::nat. (if (X = 0) then (x_i A - x_i B = x_j A - x_j B)
                             else if (X = 1) then (x_i A - x_i C = x_j A - x_j C)
                             else if (X = 2) then (x_i B - x_i C = x_j B - x_j C)
                             else False))"
       then have "P 0 = (x_i A - x_i B = x_j A - x_j B)"
 and "P 1 = (x_i A - x_i C = x_j A - x_j C)"
         and "P 2 = (x_i B - x_i C = x_j B - x_j C)" using P_def by (force, force, force)
       have "x_i A - x_i B = x_j A - x_j B \<and> x_i A - x_i C 
= x_j A - x_j C \<longrightarrow> x_i B - x_i C = x_j B - x_j C"
         by auto
       from this have 1:"P 0 \<and> P 1 \<longrightarrow> P 2" using P_def by presburger
       have "x_i A - x_i C = x_j A - x_j C \<and> x_i B - x_i C
 = x_j B - x_j C\<longrightarrow> x_i A - x_i B = x_j A - x_j B "
         by auto
       from this have 2:"P 1 \<and> P 2 \<longrightarrow> P 0" using P_def by presburger
       have "x_i A - x_i B = x_j A - x_j B \<and> x_i B - x_i C 
= x_j B - x_j C\<longrightarrow> x_i A - x_i C = x_j A - x_j C "
         by auto
       from this have 3:"P 2 \<and> P 0 \<longrightarrow> P 1" using P_def by presburger
       have swap1:"(x_i A - x_i B =x_j B - x_j A) 
\<and> (x_i A - x_i C =  x_j C - x_j A) \<longrightarrow> (x_i B - x_i C = x_j C - x_j B)"
         by auto
       have "\<not>(x_i A - x_i B = x_j A - x_j B) 
\<and> \<not>(x_i A - x_i C = x_j A - x_j C) \<longrightarrow> \<not>(x_i B - x_i C = x_j B - x_j C)"
         by (subst subt_swap_neg[symmetric], rule `\<bar>x_i A - x_i B\<bar> = \<bar>x_j B - x_j A\<bar>`, 
rule `\<bar>x_i A - x_i B\<bar> \<noteq> 0`,
         subst subt_swap_neg[symmetric], rule `\<bar>x_i A - x_i C\<bar> = \<bar>x_j C - x_j A\<bar>`,
 rule `\<bar>x_i A - x_i C\<bar> \<noteq> 0`,
         subst subt_swap_neg[symmetric], rule `\<bar>x_i B - x_i C\<bar> = \<bar>x_j C - x_j B\<bar>`, 
rule `\<bar>x_i B - x_i C\<bar> \<noteq> 0`, rule swap1)
       from this have 4:"\<not>P 0 \<and> \<not>P 1 \<longrightarrow> \<not>P 2" using P_def by presburger
       have swap2:"(x_i A - x_i C =  x_j C - x_j A)
 \<and> (x_i B - x_i C = x_j C - x_j B)\<longrightarrow> (x_i A - x_i B =x_j B - x_j A)"
         by auto
       have "\<not>(x_i A - x_i C = x_j A - x_j C)
 \<and> \<not>(x_i B - x_i C = x_j B - x_j C) \<longrightarrow> \<not>(x_i A - x_i B = x_j A - x_j B)"
         by (subst subt_swap_neg[symmetric], rule `\<bar>x_i A - x_i B\<bar> = \<bar>x_j B - x_j A\<bar>`,
 rule `\<bar>x_i A - x_i B\<bar> \<noteq> 0`,
         subst subt_swap_neg[symmetric], rule `\<bar>x_i A - x_i C\<bar> = \<bar>x_j C - x_j A\<bar>`, 
rule `\<bar>x_i A - x_i C\<bar> \<noteq> 0`,
         subst subt_swap_neg[symmetric], rule `\<bar>x_i B - x_i C\<bar> = \<bar>x_j C - x_j B\<bar>`, 
rule `\<bar>x_i B - x_i C\<bar> \<noteq> 0`, rule swap2)
       from this have 5:"\<not>P 1 \<and> \<not>P 2 \<longrightarrow> \<not>P 0" using P_def by presburger
       have swap3:"(x_i A - x_i B =x_j B - x_j A) 
\<and> (x_i B - x_i C = x_j C - x_j B)\<longrightarrow> (x_i A - x_i C =  x_j C - x_j A)"
         by auto
       have "\<not>(x_i A - x_i B = x_j A - x_j B) 
\<and> \<not>(x_i B - x_i C = x_j B - x_j C) \<longrightarrow> \<not>(x_i A - x_i C = x_j A - x_j C)"
         by (subst subt_swap_neg[symmetric], rule `\<bar>x_i A - x_i B\<bar> = \<bar>x_j B - x_j A\<bar>`, 
rule `\<bar>x_i A - x_i B\<bar> \<noteq> 0`,
         subst subt_swap_neg[symmetric], rule `\<bar>x_i A - x_i C\<bar> = \<bar>x_j C - x_j A\<bar>`, 
rule `\<bar>x_i A - x_i C\<bar> \<noteq> 0`,
         subst subt_swap_neg[symmetric], rule `\<bar>x_i B - x_i C\<bar> = \<bar>x_j C - x_j B\<bar>`, 
rule `\<bar>x_i B - x_i C\<bar> \<noteq> 0`, rule swap3)
       from this have 6:"\<not>P 2 \<and> \<not>P 0 \<longrightarrow> \<not>P 1" using P_def by presburger
       from 1 2 3 4 5 6 have "(\<forall>n. 0 \<le> n \<and> n \<le> 2 \<longrightarrow> P n) = (\<not> (\<forall>n. 0 \<le> n \<and> n \<le> 2 \<longrightarrow> \<not> P n))" 
         by (rule two_imply_third)
       then have "(P 0 \<and> P 1 \<and> P 2) \<longleftrightarrow> (\<not> (\<not>P 0 \<and> \<not>P 1 \<and> \<not>P 2))" by force
       then have prev:      "((x_i A - x_i B = x_j A - x_j B) \<and>
                         (x_i A - x_i C = x_j A - x_j C) \<and>
                         (x_i B - x_i C = x_j B - x_j C)) \<longleftrightarrow>
                      \<not> (\<not>(x_i A - x_i B = x_j A - x_j B) \<and>
                         \<not>(x_i A - x_i C = x_j A - x_j C) \<and>
                         \<not>(x_i B - x_i C = x_j B - x_j C))"
          using P_def by force
        have       "((x_i A - x_i B = x_j A - x_j B) \<and>
                     (x_i A - x_i C = x_j A - x_j C) \<and>
                     (x_i B - x_i C = x_j B - x_j C)) \<longleftrightarrow>
                  \<not> ((x_i A - x_i B = x_j B - x_j A) \<and>
                     (x_i A - x_i C = x_j C - x_j A) \<and>
                     (x_i B - x_i C = x_j C - x_j B))"
          by (subst (4) subt_swap_neg, rule `\<bar>x_i A - x_i B\<bar> = \<bar>x_j B - x_j A\<bar>`, 
rule `\<bar>x_i A - x_i B\<bar> \<noteq> 0`,
         subst (5) subt_swap_neg, rule `\<bar>x_i A - x_i C\<bar> = \<bar>x_j C - x_j A\<bar>`,
 rule `\<bar>x_i A - x_i C\<bar> \<noteq> 0`,
         subst (6) subt_swap_neg, rule `\<bar>x_i B - x_i C\<bar> = \<bar>x_j C - x_j B\<bar>`,
 rule `\<bar>x_i B - x_i C\<bar> \<noteq> 0`, rule prev)
        then consider"((x_i A - x_i B = x_j A - x_j B) \<and>
                     (x_i A - x_i C = x_j A - x_j C) \<and>
                     (x_i B - x_i C = x_j B - x_j C))"
               |"   ((x_i A - x_i B = x_j B - x_j A) \<and>
                     (x_i A - x_i C = x_j C - x_j A) \<and>
                     (x_i B - x_i C = x_j C - x_j B))"
          by fast
        then show "between_rel x_i A B C = between_rel x_j A B C"
        proof cases
          assume "((x_i A - x_i B = x_j A - x_j B) \<and> (x_i A - x_i C = x_j A - x_j C)
                                                   \<and> (x_i B - x_i C = x_j B - x_j C))"
          then show "between_rel x_i A B C = between_rel x_j A B C" using between_rel_def
          using \<open>C \<in> line A B\<close> \<open>x_j \<in> Coord (line A B)\<close> x_i_def  by force
        next
          assume "(x_i A - x_i B = x_j B - x_j A) \<and> (x_i A - x_i C = x_j C - x_j A)
                                                  \<and> (x_i B - x_i C = x_j C - x_j B)"
          then show "between_rel x_i A B C = between_rel x_j A B C" using between_rel_def
          using \<open>C \<in> line A B\<close> \<open>x_j \<in> Coord (line A B)\<close> x_i_def  by force
        qed
      next
        assume case_spliti:"\<bar>x_i A - x_i B\<bar> = 0 \<or> \<bar>x_i B - x_i C\<bar> = 0 \<or> \<bar>x_i A - x_i C\<bar> = 0"
        have casei1:"\<bar>x_i A - x_i B\<bar> = 0 \<Longrightarrow> \<not>(x_i A < x_i B \<or> x_i B <  x_i A)" by auto
        have casei2:"\<bar>x_i B - x_i C\<bar> = 0 \<Longrightarrow> \<not>(x_i C < x_i B \<or> x_i B <  x_i C)" by auto
        have casei3:"\<bar>x_i A - x_i C\<bar> = 0 \<Longrightarrow> \<not>(x_i C < x_i B \<and> x_i B <  x_i A)" by auto
        from case_spliti casei1 casei2 casei3 have "between_rel x_i A B C = False"
          using between_rel_def
           `C \<in> line A B`  x_i_def by force
        from case_spliti
        have case_splitj:"\<bar>x_j B - x_j A\<bar> = 0 \<or> \<bar>x_j C - x_j B\<bar> = 0 \<or>  \<bar>x_j C - x_j A\<bar> = 0" 
          by (subst `\<bar>x_i A - x_i B\<bar> = \<bar>x_j B - x_j A\<bar>`[symmetric],
 subst `\<bar>x_i A - x_i C\<bar> = \<bar>x_j C - x_j A\<bar>`[symmetric],
              subst `\<bar>x_i B - x_i C\<bar> = \<bar>x_j C - x_j B\<bar>`[symmetric])
        have casej1:"\<bar>x_j A - x_j B\<bar> = 0 \<Longrightarrow> \<not>(x_j A < x_j B \<or> x_j B <  x_j A)" by auto
        have casej2:"\<bar>x_j B - x_j C\<bar> = 0 \<Longrightarrow> \<not>(x_j C < x_j B \<or> x_j B <  x_j C)" by auto
        have casej3:"\<bar>x_j A - x_j C\<bar> = 0 \<Longrightarrow> \<not>(x_j C < x_j B \<and> x_j B <  x_j A)" by auto
        from case_splitj casej1 casej2 casej3
        have "between_rel x_j A B C = False" using between_rel_def
           `C \<in> line A B`  `x_j \<in> Coord (line A B)` by force
        from this `between_rel x_i A B C = False`
        show "between_rel x_i A B C = between_rel x_j A B C" by blast
      qed
    qed
  qed

definition 
"between' == (SOME between. \<forall> l \<in> Line. \<forall> A \<in> l.  \<forall> B \<in> l.  \<forall> C \<in> l. \<forall>x \<in> Coord l.
  between A B C = between_rel x A B C)"
definition 
"between == (SOME between. \<forall> A B C. \<forall>x \<in> Coord (line A B).  between A B C = between_rel x A B C)"

lemma choice3:"\<forall>a b c. \<exists>y. Q a b c y \<Longrightarrow> \<exists>f. \<forall>a b c. Q a b c (f a b c)"
proof -
  assume "\<forall>a b c. \<exists>y. Q a b c y"
  have "\<forall>a. \<exists>f. \<forall>b c. Q a b c (f b c)"
  proof (rule allI)
    fix a
    have "\<forall>b. \<exists>f. \<forall>c. Q a b c (f c)"
    proof (rule allI)
      fix b
      from `\<forall>a b c. \<exists>y. Q a b c y` have "\<forall>b c. \<exists>y. Q a b c y" by (rule spec) 
      then have "\<forall>c. \<exists>y. Q a b c y" by (rule spec) 
      then show "\<exists>f. \<forall>c. Q a b c (f c)" by (rule choice)
    qed
    then show "\<exists>f. \<forall>b c. Q a b c (f b c)"  by (rule choice)
  qed
  then show "\<exists>f. \<forall>a b c. Q a b c (f a b c)"  by (rule choice)
qed

lemma between_bestdef:"\<forall> A B C. \<forall>x \<in> Coord (line A B).  between A B C = between_rel x A B C"
proof- 
  from betweenness_independence
  have "\<forall> A B C. \<exists>between. \<forall>x\<in>Coord (line A B). between = between_rel x A B C" by simp
  then have "\<exists>between. \<forall> A B C. \<forall>x\<in>Coord (line A B). between A B C = between_rel x A B C"
    by (rule choice3) 
  then have "\<forall> A B C. \<forall>x \<in> Coord (line A B). (SOME between. \<forall> A B C. \<forall>x \<in> Coord (line A B).
 between A B C = between_rel x A B C) A B C = between_rel x A B C"
    by (subst(asm) some_eq_ex[symmetric])
  then show "\<forall> A B C. \<forall>x \<in> Coord (line A B). between A B C = between_rel x A B C" 
    by (subst between_def)
qed

lemma between_expanded_def:"\<forall>x\<in> Coord (line A B). (between A B C = 
   (if C \<in> line A B
   then x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A else False))"
proof 
  fix x
  assume "x\<in> Coord (line A B)"
  then have "between A B C = between_rel x A B C" using between_bestdef by blast
  then have "between A B C =
   (if C \<in> line A B \<and> x \<in> Coord (line A B)
   then x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A else False)" by (simp add: between_rel_def)
  from this `x\<in> Coord (line A B)` show "(between A B C = 
   (if C \<in> line A B
   then x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A else False))" by presburger
qed

lemma between_true: assumes "x \<in> Coord (line A B)" "between A B C" 
  shows "x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A" "C \<in> line A B"
proof -
  from between_expanded_def `x \<in> Coord (line A B)` `between A B C` have
    betw:"if C \<in> line A B then x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A else False"
    by blast
  show "x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A" "C \<in> line A B"
  proof (case_tac [!] "C \<in> line A B")
    assume "C \<notin> line A B"
    from `C \<notin> line A B` betw have False
      by presburger
    then show "x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A" "C \<in> line A B" by blast+
  next
    assume "C \<in> line A B"
    from betw this show "x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A" "C \<in> line A B"
      by presburger+
  qed
qed

lemma bet_imp_distinct:  assumes "between A B C"
        shows "A \<noteq> B" and "B \<noteq> C" and "A \<noteq> C"
proof -
  have "line A B \<in> Line" by (rule line_bestdef)
  from this brossard_line_measure1 obtain x where x_def: "x \<in> Coord (line A B)" by blast
  from this assms have bet_rel: "between_rel x A B C" using between_bestdef by blast
  from bet_rel show "A \<noteq> B" by (rule bet_imp_distinct_rel(1))
  from bet_rel show "B \<noteq> C" by (rule bet_imp_distinct_rel(2))
  from bet_rel show "A \<noteq> C" by (rule bet_imp_distinct_rel(3)) 
qed

lemma between_sym: "between A B C = between C B A"
proof -
  have "line A B \<in> Line" by (rule line_bestdef)
  then obtain x where x_def: "x\<in>Coord (line A B)" by (rule_tac exE,rule  brossard_line_measure1)
  have "line C B \<in> Line" by (rule line_bestdef)
  then obtain y where y_def: "y\<in>Coord (line C B)" by (rule_tac exE,rule  brossard_line_measure1)
  show ?thesis
  proof (cases "C \<in> line A B")
    assume "C \<notin> line A B" 
    show "between A B C = between C B A"
    proof (cases "A = B")
      assume "A \<noteq> B"
      from this `C \<notin> line A B` have "A \<notin> line C B" by (subst line_sym, rule not_on_line_sym)
      from this y_def have "between C B A = False" using between_expanded_def by auto
      moreover from `C \<notin> line A B` x_def have "between A B C = False" using between_expanded_def 
        by auto    
      ultimately show "between A B C = between C B A" by simp    
    next
      assume "A = B"
      then have "between A B C = False" using bet_imp_distinct by blast
      moreover from `A = B` have "between C B A = False" using bet_imp_distinct by blast
      ultimately show "between A B C = between C B A" by simp
    qed
  next
    assume "C \<in> line A B"
    show "between A B C = between C B A"
    proof (cases "C = B")
      assume "C \<noteq> B"
      from this `C \<in> line A B` have "A \<in> line C B" by (subst(asm) line_sym, rule_tac on_line_sym)
      from `C \<in> line A B` line_bestdef `C \<noteq> B` have  "line A B = line C B" using line_bestdef_inv 
        by meson
      from `C \<in> line A B` x_def 
      have "between A B C = (x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A)"
        using between_expanded_def by simp
      also have "... = (x C < x B \<and> x B < x A \<or> x A < x B \<and> x B < x C)" by safe
      also from `line A B = line C B` `A \<in> line C B` x_def have "... = between C B A"
        using between_expanded_def by simp
      finally show "between A B C = between C B A" by simp
    next
      assume "C = B"
      then have "between A B C = False" using bet_imp_distinct by blast
      moreover from `C = B` have "between C B A = False" using bet_imp_distinct by blast
      ultimately show "between A B C = between C B A" by simp
    qed
  qed
qed

lemma between_otherside: assumes "A \<noteq> X" shows "\<exists>B \<in> line X A. between A X B"
proof -
  have "line X A \<in> Line" by (rule line_bestdef)
  then obtain x where x_def: "x\<in>Coord (line X A)" by (rule_tac exE,rule  brossard_line_measure1)  
  from `line X A \<in> Line` x_def have "bij_betw x (line X A) (UNIV::real set)" 
    by (rule brossard_line_measure2)
  from `bij_betw x (line X A) UNIV` have "x ` (line X A) = (UNIV::real set)" 
    by (subst(asm) bij_betw_def, rule_tac conjunct2)
  from this have im:"{y. \<exists>z\<in>(line X A). y = x z} = UNIV" by (subst(asm) image_def)
  from x_def `A \<noteq> X` have "x A \<noteq> x X"
    by (subst(asm) coordfn_preserves_distinctness, auto simp: line_bestdef)
  then consider "x A > x X" | "x A < x X" by linarith
  then show ?thesis
  proof (cases)
    assume "x A > x X"
    from im obtain B where "B \<in> (line X A)" and "x X -1 = x B" by blast
    from this `x A > x X` have "x A > x X \<and> x X > x B" by simp
    from this x_def between_expanded_def `B \<in> (line X A)` line_sym have "between A X B" by force
    from this `B \<in> (line X A)` show ?thesis by blast
  next
    assume "x X > x A"
    from im obtain B where "B \<in> (line X A)" and "x X + 1 = x B" by blast
    from this `x X > x A` have "x B > x X \<and> x X > x A" by simp
    from this x_def between_expanded_def `B \<in> (line X A)` line_sym have "between A X B" by force
    from this `B \<in> (line X A)` show ?thesis by blast
  qed
qed

lemma between_imp_collinear: assumes "between A X B" shows "B \<in> line A X"
proof -
  have "line A X \<in> Line" by (rule line_bestdef)
  then obtain x where x_def: "x\<in>Coord (line A X)" by (rule_tac exE,rule  brossard_line_measure1)  
 from `between A X B` x_def show "B \<in> line A X" using between_expanded_def by meson
qed


lemma sameside_eq_notbetween: assumes "between A X B" "between A X P" 
                                shows "\<not> between B X P"
proof -
  have "line A X \<in> Line" by (rule line_bestdef)
  then obtain x where x_def: "x\<in>Coord (line A X)" by (rule_tac exE,rule  brossard_line_measure1)
  from `between A X B` have "B \<in> line A X" by (rule between_imp_collinear)
  from `between A X P` have "P \<in> line A X" by (rule between_imp_collinear)
  from `between A X B` have "X \<noteq> B" by (rule bet_imp_distinct)
  from `between A X P` have "X \<noteq> P" by (rule bet_imp_distinct)
  show ?thesis
  proof (cases "B = P")
    assume "B = P"
    from this show "\<not> between B X P" using bet_imp_distinct by blast  
  next
    assume "B \<noteq> P"
    from `B \<in> line A X` line_bestdef `X \<noteq> B` have  "line A X = line B X" using line_bestdef_inv 
      by presburger
    from x_def `between A X B` have "x A < x X \<and> x X < x B \<or> x B < x X \<and> x X < x A"
      by (rule between_true)
    moreover from x_def `between A X P` have "x A < x X \<and> x X < x P \<or> x P < x X \<and> x X < x A"
      by (rule between_true)  
    ultimately have "\<not>(x B < x X \<and> x X < x P \<or> x P < x X \<and> x X < x B)" 
    using `B \<noteq> P` `X \<noteq> B` `X \<noteq> P` by linarith
    from this x_def `line A X = line B X` show "\<not> between B X P" using between_expanded_def by simp
  qed
qed

definition "sameside A B X = (between X B A \<or> between X A B)"


lemma between_trans: assumes "between A B C" shows "between B C D \<Longrightarrow> between A C D"
"between A C D \<Longrightarrow> between B C D"
proof -
  obtain x where x_def:"x \<in> Coord (line A B)"
    using brossard_line_measure1 line_bestdef(1) by blast
  from x_def `between A B C`
  have 1:"x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A" "C \<in> line A B" 
    by (rule_tac [!] between_true)
  from this have "line A B = line B C" using line_bestdef_inv line_bestdef by blast
  have 2:"(line A B) \<in> Line" "A \<in> line A B" by (rule_tac[!] line_bestdef)
  from 1 have "A \<noteq> C" by force
  from 1 2 this have "line A B = line A C" using line_bestdef_inv by blast
  show "between B C D \<Longrightarrow> between A C D"
  proof-
    assume "between B C D"
    from x_def have "x \<in> Coord (line B C)" by (subst(asm) `line A B = line B C`)
    from this `between B C D` have 2:"x B < x C \<and> x C < x D \<or> x D < x C \<and> x C < x B" "D \<in> line B C"
      by (rule_tac [!] between_true)
    from 1 2 have 3:"x A < x C \<and> x C < x D \<or> x D < x C \<and> x C < x A" by linarith
    from this `C \<in> line A B` `line A B = line B C` have "line A C = line B C"
      using line_bestdef_inv line_bestdef by blast
    from `D \<in> line B C` have "D \<in> line A C" by (subst `line A C = line B C`)
    from `x \<in> Coord (line B C)` have "x \<in> Coord (line A C)" by (subst `line A C = line B C`)
    from 3 this `D \<in> line A C` show "between A C D" using between_expanded_def by simp
  qed
  show "between A C D \<Longrightarrow> between B C D"
  proof-
    assume "between A C D"
    from x_def have "x \<in> Coord (line A C)" by (subst(asm) `line A B = line A C`)
    from this `between A C D` have 2:"x A < x C \<and> x C < x D \<or> x D < x C \<and> x C < x A" "D \<in> line A C"
      by (rule_tac [!] between_true)
    from 1 2 have 3:"x B < x C \<and> x C < x D \<or> x D < x C \<and> x C < x B" by linarith
    from `line A B = line A C`[symmetric] `line A B = line B C` have "line A C = line B C"
       by (rule_tac trans)
    from `D \<in> line A C` have "D \<in> line B C" by (subst(asm) `line A C = line B C`)
    from `x \<in> Coord (line A C)` have "x \<in> Coord (line B C)" by (subst(asm) `line A C = line B C`)
    from 3 this `D \<in> line B C` show "between B C D" using between_expanded_def by simp
  qed
qed

lemma assumes "sameside A P X" shows 
sameside_same_between: "(\<lambda> Q. between A X Q) = (\<lambda> Q. between P X Q)" and
sameside_same_line: "line X A = line X P" 
proof (case_tac [!] "between X P A")
  assume "between X P A" 
  from `between X P A` have "between A P X" by (subst between_sym)
  then have "X \<in> line A P" by (rule between_imp_collinear)
  from `between X P A`have "X \<noteq> A" by (rule bet_imp_distinct)
  from this `X \<in> line A P` have "P \<in> line X A" by (rule_tac on_line_sym)
  from `between A P X`have "P \<noteq> X" by (rule bet_imp_distinct)
  from this `P \<in> line X A` show "line X A = line X P"
    by (rule_tac line_independence(4))
  show "(\<lambda> Q. between A X Q) = (\<lambda> Q. between P X Q)"
  proof (rule ext, rule iffI)
    fix Q
    assume "between A X Q"
    from `between A P X` `between A X Q` show "between P X Q" by (rule between_trans)
  next
    fix Q
    assume "between P X Q"
    from `between A P X` `between P X Q` show "between A X Q" by (rule between_trans)
  qed
next assume "\<not>between X P A"
  moreover from assms have "between X P A \<or> between X A P" by (subst(asm) sameside_def)
  ultimately have "between X A P" by blast
  from `between X A P` have "between P A X" by (subst between_sym)
   from `between X A P` have "P \<in> line X A" by (rule between_imp_collinear)
  from `between P A X` have "P \<noteq> X" by (rule bet_imp_distinct)
  from this `P \<in> line X A` show "line X A = line X P"
    by (rule_tac line_independence(4))
  show "(\<lambda> Q. between A X Q) = (\<lambda> Q. between P X Q)"
  proof (rule ext, rule iffI)
    fix Q
    assume "between A X Q"
    from `between P A X` `between A X Q` show "between P X Q" by (rule between_trans)
  next
    fix Q
    assume "between P X Q"
    from `between P A X` `between P X Q` show "between A X Q" by (rule between_trans)
  qed  
qed

definition "distance A B == (SOME distance. \<exists>x \<in> Coord (line A B). distance = distance_rel x A B)"

lemma distance_bestdef: "\<exists>x \<in> Coord (line A B). distance A B = distance_rel x A B"
proof -
  have "line A B \<in> Line" by (rule line_bestdef(1))
  then have x_def:"\<exists>x. x \<in> Coord (line A B)" by (rule  brossard_line_measure1)
  from this have "\<exists>x \<in> Coord (line A B). distance_rel x A B = distance_rel x A B" by blast
  then have "\<exists>distance. \<exists>x \<in> Coord (line A B). distance = distance_rel x A B" by blast
  from this 
  have "\<exists>x \<in> Coord (line A B). (SOME distance. \<exists>x \<in> Coord (line A B). distance 
= distance_rel x A B) = distance_rel x A B"
    by (subst(asm) some_eq_ex[symmetric])
  then show "\<exists>x \<in> Coord (line A B). distance A B = distance_rel x A B" by (subst distance_def)
qed

lemma distance_expanded_def: "\<exists>x \<in> Coord (line A B). distance A B = \<bar>x A - x B\<bar>"
proof -
  from distance_bestdef obtain x where "x \<in> Coord (line A B)" 
and "distance A B = distance_rel x A B" by blast
  from this `x \<in> Coord (line A B)` have "distance A B = \<bar>x A - x B\<bar>" 
    by (subst distance_rel_def[symmetric])
  from this `x \<in> Coord (line A B)` show ?thesis by blast
qed

lemma distance_0_imp_eq:assumes "distance P Q = 0" shows "P = Q"
proof -
  obtain x where "x\<in>Coord (line P Q)" 
"distance P Q = \<bar>x P - x Q\<bar>" using distance_expanded_def by blast
  from this assms have "x P = x Q" by fastforce
  moreover from `x\<in>Coord (line P Q)` have "(P = Q) = (x P = x Q)" using line_bestdef
    by (rule_tac coordfn_preserves_distinctness)
  ultimately show "P = Q" by simp
qed

lemma noncollinear_imp_pos_distance:
  assumes "\<not>(collinear P Q R)" shows "distance P Q > 0" (*use collinear sym to get more cases*)
proof (rule ccontr)
  assume "\<not> 0 < distance P Q"
  obtain x where "distance P Q = \<bar>x P - x Q\<bar>" using distance_expanded_def by blast
  from this `\<not> 0 < distance P Q` have "distance P Q = 0" by force
  then have "P = Q" by (rule distance_0_imp_eq)
  then have "collinear P Q R" using collinear_def by simp
  from this assms show False by contradiction
qed

lemma betweenness_uniqueness:
"\<And> A B C. \<forall>x\<in>Coord (line A B). b A B C = between_rel x A B C \<Longrightarrow> b A B C = between A B C"
proof -
  fix A B C
  assume b_def:"\<forall>x\<in>Coord (line A B). b A B C = between_rel x A B C"
  from between_bestdef have bet_def: "\<forall>x\<in>Coord (line A B). between A B C = between_rel x A B C" 
    by simp
  have "line A B \<in> Line" 
    by (rule line_bestdef(1))
  then obtain x where x_def:"x \<in> Coord (line A B)" 
    by (rule_tac exE, rule  brossard_line_measure1)
  from x_def b_def bet_def have "b A B C = between_rel x A B C" 
and "between A B C = between_rel x A B C"
    by auto
  then show "b A B C = between A B C" by blast
qed

lemma distance_bestdef_inv: 
  assumes "distance A B = \<bar>x A - x B\<bar>" " x\<in>Coord (line A B)" 
  shows" (distance A B = distance_rel x A B)"
proof -
  thm line_bestdef_inv
  from distance_bestdef obtain y where "y\<in>Coord (line A B)"
    and y_def: "distance A B = distance_rel y A B" by blast
  from `y\<in>Coord (line A B)` `x\<in>Coord (line A B)` line_bestdef
  have "\<bar>x A - x B\<bar> = \<bar>y A - y B\<bar>" using brossard_line_measure_2_3 by blast
  from this `x\<in>Coord (line A B)` `y\<in>Coord (line A B)` y_def distance_rel_def 
  show "distance A B = distance_rel x A B" by presburger
qed


lemma consistent_coordfn: assumes "(\<exists>l \<in> Line. A \<in> l \<and> C \<in> l \<and> x \<in> Coord(l))"
      shows "distance A C = \<bar>x A - x C\<bar>"
proof (cases "A=C")
  assume "A\<noteq>C"
  from assms(1) obtain l where l_def:"l \<in> Line \<and> A \<in> l \<and> C \<in> l \<and> x \<in> Coord(l)" by blast
  from this `A\<noteq>C` have "l = line A C" using line_bestdef_inv by presburger
  from l_def this have "x \<in> Coord(line A C)" by blast
  have "\<exists>y \<in> Coord(line A C). distance A C = distance_rel y A C" by (rule distance_bestdef)
  from this 
  obtain y where "y \<in> Coord(line A C)" and "distance A C = distance_rel y A C" by auto
  have "(line A C) \<in> Line" and "A \<in> line A C" and "C \<in> line A C" by (rule_tac[!] line_bestdef)
  from this `x \<in> Coord(line A C)` have "\<bar>x A - x C\<bar> = \<bar>y A - y C\<bar>" 
    using brossard_line_measure_2_3 `y \<in> Coord(line A C)` by blast
  from this `y \<in> Coord(line A C)` `distance A C = distance_rel y A C` 
  show ?thesis using distance_rel_def by simp
next
  assume "A=C"
  moreover obtain z where "distance A C = \<bar>z A - z C\<bar>" using distance_expanded_def by blast
  ultimately have "distance A C = 0" by simp
  also have "... = \<bar>x A - x C\<bar>" using `A=C` by simp
  finally show ?thesis by simp
qed

lemma collinear_triangle:
"collinear A B C \<Longrightarrow> 
(between A B C \<or> A=B \<or> B=C) = ((distance A B) + (distance B C) = (distance A C))"
proof 
  assume "collinear A B C"
  assume assm2: "between A B C \<or> A = B \<or> B = C"
  then consider (a) "between A B C" | (b) "A=B" | (c) "B=C" by linarith
  then show "distance A B + distance B C = distance A C"
  proof (cases)
    assume "between A B C" 
    then have "A\<noteq>B" by (rule bet_imp_distinct)
    from this `collinear A B C` have "C \<in> (line A B)" using collinear_def by auto
    from distance_expanded_def obtain x where "x \<in> Coord (line A B)"
 and "((distance A B) = \<bar>x A - x B\<bar>)"
      by blast
    from line_bestdef `C \<in> (line A B)` `x \<in> Coord (line A B)` have "((distance A C) = \<bar>x A - x C\<bar>)"
      using consistent_coordfn by blast
    from line_bestdef `C \<in> (line A B)` `x \<in> Coord (line A B)` have "((distance B C) = \<bar>x B - x C\<bar>)"
      using consistent_coordfn by blast
    from `x \<in> Coord (line A B)` `between A B C`
    have "x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A" by (rule between_true)
    then have "\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar>= \<bar>x A - x C\<bar>" by linarith
    then show  "((distance A B) + (distance B C) = (distance A C))"
      by (subst `distance A C = \<bar>x A - x C\<bar>`, subst `distance B C = \<bar>x B - x C\<bar>`, 
          subst `distance A B = \<bar>x A - x B\<bar>`)  
  next 
    assume "A=B"
    obtain y where "distance A B = \<bar>y A - y B\<bar>" using distance_expanded_def by blast
    from this `A=B` have "distance A B = 0" by fastforce
    from this `A=B` show "((distance A B) + (distance B C) = (distance A C))" by force
  next
    assume "B=C"
    obtain y where "distance B C = \<bar>y B - y C\<bar>" using distance_expanded_def by blast
    from this `B=C` have "distance B C = 0" by fastforce
    from this `B=C` show "((distance A B) + (distance B C) = (distance A C))" by force
  qed
next
  assume "collinear A B C"
  assume assm3: "(distance A B) + (distance B C) = (distance A C)"
  then consider (a) "A\<noteq>B \<and> B\<noteq>C \<and> A\<noteq>C" | (b) "A=B" | (c) "B=C"  | (d) "A\<noteq>B \<and> B\<noteq>C \<and> A=C"
    by linarith
  then show "between A B C \<or> A=B \<or> B=C"
  proof (cases)
    assume distinct: "A\<noteq>B \<and> B\<noteq>C \<and> A\<noteq>C"
    from this `collinear A B C` have "C \<in> (line A B)" using collinear_def by auto
    from distance_expanded_def obtain x where "x \<in> Coord (line A B)" 
and "((distance A B) = \<bar>x A - x B\<bar>)"
      by blast
    from line_bestdef `C \<in> (line A B)` `x \<in> Coord (line A B)` have "((distance A C) = \<bar>x A - x C\<bar>)"
      using consistent_coordfn by blast
    from line_bestdef `C \<in> (line A B)` `x \<in> Coord (line A B)` have "((distance B C) = \<bar>x B - x C\<bar>)"
      using consistent_coordfn by blast   
    from assm3 have "\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar>= \<bar>x A - x C\<bar>"
      by (subst `distance A C = \<bar>x A - x C\<bar>`[symmetric], 
subst `distance B C = \<bar>x B - x C\<bar>`[symmetric], 
          subst `distance A B = \<bar>x A - x B\<bar>`[symmetric])
    from distinct coordfn_preserves_distinctness `x \<in> Coord (line A B)` `C \<in> (line A B)` 
line_bestdef
    have "x A \<noteq> x B \<and> x B \<noteq> x C \<and> x A \<noteq> x C" by blast
    then consider (a) "x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A" 
                | (b) "x B < x A \<and> x A < x C \<or> x C < x A \<and> x A < x B"
                | (c) "x A < x C \<and> x C < x B \<or> x B < x C \<and> x C < x A" by linarith
    then show "between A B C \<or> A=B \<or> B=C"
    proof cases
      assume "x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A"
      from this `C \<in> (line A B)` `x \<in> Coord (line A B)` have "between A B C"
        using between_expanded_def by force
      then show ?thesis by simp
    next
      assume "x B < x A \<and> x A < x C \<or> x C < x A \<and> x A < x B"
      then have "\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar>> \<bar>x A - x C\<bar>" by fastforce
      from this `\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar>= \<bar>x A - x C\<bar>` have False by auto
      then show ?thesis by simp
    next
      assume "x A < x C \<and> x C < x B \<or> x B < x C \<and> x C < x A"
      then have "\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar>> \<bar>x A - x C\<bar>" by fastforce
      from this `\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar>= \<bar>x A - x C\<bar>` have False by auto
      then show ?thesis by simp
    qed
  next
    assume "A=B" then show ?thesis by simp
  next
    assume "B=C" then show ?thesis by simp
  next
    assume cond: "A\<noteq>B \<and> B\<noteq>C \<and> A=C"
    from this `collinear A B C` have "C \<in> (line A B)" using collinear_def by auto
    from distance_expanded_def obtain x where "x \<in> Coord (line A B)"
 and "((distance A B) = \<bar>x A - x B\<bar>)"
      by blast
    from line_bestdef `C \<in> (line A B)` `x \<in> Coord (line A B)` have "((distance A C) = \<bar>x A - x C\<bar>)"
      using consistent_coordfn by blast
    from line_bestdef `C \<in> (line A B)` `x \<in> Coord (line A B)` have "((distance B C) = \<bar>x B - x C\<bar>)"
      using consistent_coordfn by blast   
    from assm3 have sum: "\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar>= \<bar>x A - x C\<bar>"
      by (subst `distance A C = \<bar>x A - x C\<bar>`[symmetric], 
subst `distance B C = \<bar>x B - x C\<bar>`[symmetric], 
          subst `distance A B = \<bar>x A - x B\<bar>`[symmetric])
    from cond coordfn_preserves_distinctness `x \<in> Coord (line A B)` line_bestdef
    have "x A \<noteq> x B \<and> x B \<noteq> x C" by blast
    then have "\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar> >0" by linarith
    moreover from cond have "\<bar>x A - x C\<bar>=0" by force
    ultimately have "\<bar>x A - x B\<bar>+ \<bar>x B - x C\<bar> > \<bar>x A - x C\<bar>" by presburger
    from this sum have False by auto
    then show ?thesis by simp
  qed
qed

lemma noncollinear_imp_dist:"\<not> collinear P1 Q1 R1 \<Longrightarrow> P1\<noteq>Q1 \<and> Q1\<noteq>R1 \<and> R1\<noteq>P1"
    using collinear_def line_bestdef(2) line_bestdef(3) by auto
 
lemma collinear_choice_of_between: assumes "collinear A X P" "A\<noteq>X" "A\<noteq>P" "P\<noteq>X"
  shows "between A P X \<or> between A X P \<or> between P A X" 
proof -
  thm between_expanded_def
  have "line A P \<in> Line" by (rule line_bestdef)
  then obtain x where x_def:"x \<in> Coord (line A P)"
    by (rule_tac exE, rule brossard_line_measure1)
  have "X \<in> line A P" using `collinear A X P`
    using assms(3) collinear_bestdef1 line_bestdef_inv by blast
  from `line A P \<in> Line` `A\<noteq>X` this have "line A P = line A X"
    using line_bestdef_inv  line_bestdef(2) by blast
  have "P \<in> line A X"
    using assms(1) assms(2) collinear_def by blast
  have "A \<in> line P X" using `collinear A X P` \<open>X \<in> line A P\<close> assms(2) assms(4) on_line_sym by auto 
  from `A\<noteq>X` this  have "line P X = line A X" using line_bestdef_inv  line_bestdef
    by simp
  from `A\<noteq>X` `A\<noteq>P` `P\<noteq>X` x_def `line A P = line A X` `line P X = line A X`
  have "x A \<noteq> x X" "x P \<noteq> x X" "x A \<noteq> x P" using coordfn_preserves_distinctness line_bestdef
    by blast+
  then consider "x A < x X \<and> x X < x P \<or> x P < x X \<and> x X < x A" |
           "x X < x A \<and> x A < x P \<or> x P < x A \<and> x A < x X" |
           "x A < x P \<and> x P < x X \<or> x X < x P \<and> x P < x A"
    by argo
  then show ?thesis
  proof (cases)
    case 1
    from this `P \<in> line A X` show ?thesis using between_expanded_def
     \<open>line A P = line A X\<close> x_def by auto
  next
    case 3
    from this `X \<in> line A P` show ?thesis using between_expanded_def
     x_def by auto
  next
    case 2
    from this show ?thesis using between_expanded_def
     line_sym x_def \<open>X \<in> line A P\<close> by auto
  qed
qed


definition "isHalfLine H = (\<exists> A X. H ={P. (\<not>between A X P \<and> P \<in> line X A)} \<and> A \<noteq> X)"

definition "HalfLine = {x. isHalfLine x}"

lemma HalfLine_bestdef: "h \<in> HalfLine = isHalfLine h"
  by (simp add: HalfLine_def)

definition "halfline X A = (if X \<noteq> A then {P. \<not>between A X P \<and> P \<in> line X A}
          else SOME h. \<exists>B \<in> line X A.  h = {P. \<not>between B X P \<and> P \<in> line X A} \<and> B\<noteq>X)"


lemma halfline_nocase_def: 
"\<exists>B\<in> line X A. halfline X A = {P. \<not> between B X P \<and> P \<in> line X A} \<and> B \<noteq> X" 
proof (case_tac [!] "X=A")
  assume "X \<noteq> A"
  moreover from this halfline_def have "halfline X A = {P. \<not>between A X P \<and> P \<in> line X A}" by simp 
  moreover have "A \<in> line X A" by (rule line_bestdef(3))
  ultimately show ?thesis by blast
next
  assume "X = A"
  then have halflineXA_def: 
"halfline X A = (SOME h. \<exists>B\<in>line X A. h = {P. \<not> between B X P \<and> P \<in> line X A} \<and> B \<noteq> X)"
    using halfline_def by auto
  have "line X A \<in> Line" by (rule line_bestdef(1))
  then obtain B where "B \<in> line X A \<and> B \<noteq> X" using two_points_on_line by blast
  then have "\<exists>h. \<exists>B\<in>line X A. h = {P. \<not> between B X P \<and> P \<in> line X A} \<and> B \<noteq> X" by blast
  then show "\<exists>B\<in> line X A. halfline X A = {P. \<not> between B X P \<and> P \<in> line X A} \<and> B \<noteq> X" 
    by (subst halflineXA_def, rule someI_ex)
qed


lemma halfline_bestdef:
shows"A \<in> halfline X A" and "X \<in> halfline X A" and "(halfline X A) \<in> HalfLine"
proof (case_tac [!] "X=A")
  assume "X \<noteq> A"
  from this halfline_def have "halfline X A = {P. \<not>between A X P \<and> P \<in> line X A}" by simp
  from this `X \<noteq> A` isHalfLine_def show "(halfline X A) \<in> HalfLine" 
    by (subst HalfLine_bestdef, auto)
  have "line A X \<in> Line" by (rule line_bestdef(1))
  then obtain x where x_def:"x \<in> Coord (line A X)" by (rule_tac exE, rule  brossard_line_measure1)
  then have "between A X A = between_rel x A X A" by (simp add: between_bestdef)
  moreover from bet_imp_distinct_rel have "\<not>between_rel x A X A" by blast
  ultimately have "\<not>between A X A" by blast
  from this `X \<noteq> A` line_bestdef show "A \<in> halfline X A" by (simp add: halfline_def)
  from x_def have "between A X X = between_rel x A X X" by (simp add: between_bestdef)
  moreover from bet_imp_distinct_rel have "\<not>between_rel x A X X" by blast
  ultimately have "\<not>between A X X" by blast
  from this `X \<noteq> A` line_bestdef show "X \<in> halfline X A" by (simp add: halfline_def)
next 
  assume "X = A"
  have "\<exists>B\<in>line X A. halfline X A = {P. \<not> between B X P \<and> P \<in> line X A} \<and> B \<noteq> X" 
    by (rule halfline_nocase_def) 
  then obtain B where "B\<in>line X A" and B_def: "halfline X A = {P. \<not> between B X P \<and> P \<in> line X A}"
    and "B \<noteq> X" by blast
  from `B\<in>line X A` `B \<noteq> X` have "line X A = line X B" using line_bestdef_inv line_bestdef
    by presburger
  from this B_def `B \<noteq> X` have halflineXA_def: 
"halfline X A = {P. \<not> between B X P \<and> P \<in> line X B}\<and>B \<noteq> X"
    by presburger
  then show "(halfline X A) \<in> HalfLine" using isHalfLine_def by (subst HalfLine_bestdef, blast)
  have "X\<in>line X B" by (subst `line X A = line X B`[symmetric], rule line_bestdef(2))
  from bet_imp_distinct have "\<not>between B X X" by blast
  from this `X\<in>line X B` halflineXA_def show "X \<in> halfline X A" by blast
  from this show "A \<in> halfline X A" by (subst(asm) `X = A`)
qed

lemma halfline_propersubset:"halfline X A \<subset> line X A"
proof -
  from halfline_nocase_def obtain C
    where "C \<in>line X A" and halflineXA_def:"halfline X A = {P. \<not> between C X P \<and> P \<in> line X A}" 
and "C \<noteq> X"
    by blast
  then have "halfline X A \<subseteq> line X A" by auto
  have "line X C \<in> Line" by (rule line_bestdef(1))
  then obtain x where x_def:"x \<in> Coord (line X C)" by (rule_tac exE, rule  brossard_line_measure1)
  have "C \<in> line X C" and "X \<in> line X C" by (rule_tac [!] line_bestdef)
  from `line X C \<in> Line` `x \<in> Coord (line X C)` have "bij_betw x (line X C) UNIV" 
    by (rule brossard_line_measure2)
  then have "inj_on x (line X C)" using bij_betw_def by auto
  from this `C \<noteq> X` `C \<in> line X C` `X \<in> line X C` have "x X \<noteq> x C" using inj_on_def by metis
  then have "x X < x C \<or> x C < x X " by linarith
  then obtain y where "(y < x X \<and> x X < x C) \<or> (x C < x X \<and> x X < y)" 
    by (meson linordered_field_no_lb linordered_field_no_ub)
  from `bij_betw x (line X C) UNIV`  have "x ` (line X C) = UNIV"
    by (subst(asm) bij_betw_def, rule_tac conjunct2)
  from this have "{y. \<exists>z\<in>(line X C). y = x z} = UNIV" by (subst(asm) image_def)
  from this obtain B where "B \<in> line X C" and "y = x B" by blast
  moreover from `C\<in>line X A` `C \<noteq> X` have "line X A = line X C" using line_bestdef_inv line_bestdef
    by presburger
  ultimately have "B \<in> line X A" by blast
  from `y = x B` `(y < x X \<and> x X < x C) \<or> (x C < x X \<and> x X < y)`
  have "(x B < x X \<and> x X < x C) \<or> (x C < x X \<and> x X < x B)" by fast
  from this `x \<in> Coord (line X C)` `B \<in> line X C` line_sym have "between C X B" 
    using between_expanded_def by force
  from this halflineXA_def have  "B \<notin> halfline X A" by blast
  from this `B \<in> line X A` `halfline X A \<subseteq> line X A` show "halfline X A \<subset> line X A" by blast
qed

lemma ex_pt_for_real: assumes "l \<in> Line" "x \<in> Coord l" shows "\<exists> P \<in> l. x P = r"
proof -
  from assms have "bij_betw x l UNIV" by (rule brossard_line_measure2)
  from this have "x ` l = UNIV" by (subst(asm) bij_betw_def, rule_tac conjunct2)
  from this have "{y. \<exists>z\<in>l. y = x z} = UNIV" by (subst(asm) image_def)
  from this obtain P where "P \<in> l" and "r = x P" by blast
  then show ?thesis by blast
qed

lemma assumes "between X P A \<or> between X A P" "P \<in> line X A"
        shows "P \<in> halfline X A"
oops

lemma brossards_halfline_def: assumes "X\<noteq>A"
  shows "halfline X A = {P. \<not> between A X P \<and> P \<in> line X A}"
  using halfline_def assms by presburger


lemma halfline_distinct_def: "(g \<in> HalfLine) = (\<exists>A X. g = halfline X A \<and> A \<noteq> X)"
proof
  assume "g \<in> HalfLine"
  then have "\<exists>A X. g = {P. \<not> between A X P \<and> P \<in> line X A} \<and> A \<noteq> X" 
    by (subst(asm) HalfLine_bestdef, subst(asm) isHalfLine_def)
  from this brossards_halfline_def show "\<exists>A X. g = halfline X A \<and> A \<noteq> X" by metis
next
  assume "\<exists>A X. g = halfline X A \<and> A \<noteq> X"
  from this halfline_bestdef(3) show "g \<in> HalfLine" by (subst(asm) HalfLine_bestdef, blast)
qed

lemma ex_unique_line_halfline: assumes "h \<in> HalfLine" shows "\<exists>!l \<in> Line. h \<subset> l"
proof - 
  from assms have "\<exists>A X. h = halfline X A \<and> A \<noteq> X" by (subst(asm) halfline_distinct_def)
  then obtain A X where "h = halfline X A" "X \<noteq> A" by blast
  from `X \<noteq> A` have "A \<in> halfline X A" "X \<in> halfline X A" by (rule_tac[!] halfline_bestdef)
  have "h \<subset> line X A" by (subst `h = halfline X A`, rule halfline_propersubset)
  have "line X A \<in> Line" by (rule line_bestdef)
  have unique:"\<forall>l \<in> Line. h \<subset> l \<longrightarrow> l = line X A"
  proof (rule ballI, rule impI)
    fix l assume "l \<in> Line"
    assume "h \<subset> l"
    from this `A \<in> halfline X A` have "A \<in> l" by (subst(asm) `h = halfline X A`, rule_tac psubsetD)
    from `h \<subset> l` `X \<in> halfline X A` have "X \<in> l" 
      by (subst(asm) `h = halfline X A`, rule_tac psubsetD)
    from `l \<in> Line` `X \<in> l` `A \<in> l` `X \<noteq> A` show "l = line X A" by (rule line_bestdef_inv)
  qed
  from `h \<subset> line X A` `line X A \<in> Line` unique show "\<exists>!l. l \<in> Line \<and> h \<subset> l" by metis
qed

lemma halfline_independence:assumes "B \<in> halfline X A" "B \<noteq> X" shows "halfline X A = halfline X B"
proof -
  from halfline_nocase_def obtain C where "C\<in>line X A" and
  halflineXA_def: "halfline X A = {P. \<not> between C X P \<and> P \<in> line X A}" "C \<noteq> X" by blast
  from assms(2) have halflineXB_def:"halfline X B = {P. \<not> between B X P \<and> P \<in> line X B}" 
    using halfline_def by auto
  from assms(1) halflineXA_def have "\<not> between C X B" by blast
  from assms(1) halflineXA_def have "B\<in>line X A" by blast
  from `C\<in>line X A` `C \<noteq> X` have "line X A = line X C" using line_bestdef_inv line_bestdef 
    by presburger
  moreover from `B\<in>line X A` `B \<noteq> X` have "line X A = line X B" using line_bestdef_inv line_bestdef
    by presburger
  ultimately have "line C X = line B X" using line_sym by simp
  have "\<forall>P\<in>line X A. between B X P = between C X P"
  proof
    fix P
    assume "P \<in> line X A"
    have "line B X \<in> Line" by (rule line_bestdef)
    then obtain x where "x\<in>Coord (line B X)" by (rule_tac exE,rule  brossard_line_measure1)
    from `B\<in>line X A` have "B \<in> line C X" by (subst line_sym, subst(asm) `line X A = line X C`)
    from `x\<in>Coord (line B X)` have "x\<in>Coord (line C X)" by (subst `line C X = line B X`)
    from `x\<in>Coord (line C X)` `B \<in> line C X` `\<not> between C X B` 
    have "\<not>(x C < x X \<and> x X < x B \<or> x B < x X \<and> x X < x C)" using between_expanded_def by auto
    moreover from `x\<in>Coord (line C X)` `B \<in> line C X` line_bestdef `C \<noteq> X` `B \<noteq> X`
    coordfn_preserves_distinctness have "x C \<noteq> x X" "x B \<noteq> x X" by (blast, blast)
    ultimately have "(x C > x X \<or> x X > x B) \<and> (x C < x X \<or> x X < x B)" by linarith
    then have BC_onsameside_X:"(x X > x B \<and> x C < x X) \<or> (x X < x B \<and> x C > x X)" by linarith
    show "between B X P = between C X P"
    proof safe
      assume "between B X P"
      from `x\<in>Coord (line B X)` `between B X P`
      have "x B < x X \<and> x X < x P \<or> x P < x X \<and> x X < x B" 
        by (rule between_true)
      from this  BC_onsameside_X
      have betweenCXP_unfolded:"x C < x X \<and> x X < x P \<or> x P < x X \<and> x X < x C" by linarith
      from `P \<in> line X A` have "P \<in> line C X" by (subst line_sym, subst(asm) `line X A = line X C`)
      from `x\<in>Coord (line C X)` this betweenCXP_unfolded show "between C X P"
        using between_expanded_def by auto
    next
      assume "between C X P"
      from `P \<in> line X A` have "P \<in> line C X" by (subst line_sym, subst(asm) `line X A = line X C`)
      from this `x\<in>Coord (line C X)` `between C X P`
      have "x C < x X \<and> x X < x P \<or> x P < x X \<and> x X < x C" 
        using between_expanded_def by auto
      from this BC_onsameside_X
      have betweenBXP_unfolded:"x B < x X \<and> x X < x P \<or> x P < x X \<and> x X < x B" by linarith
      from `P \<in> line X A` have "P \<in> line B X" by (subst line_sym, subst(asm) `line X A = line X B`)
      from `x\<in>Coord (line B X)` this betweenBXP_unfolded show "between B X P"
        using between_expanded_def by auto
    qed
  qed
  from this halflineXA_def halflineXB_def `line X A = line X B`
  show "halfline X A = halfline X B" by blast
qed

lemma halfline_points_on_line: assumes "h \<in> HalfLine" "A \<in> h" "A \<noteq> B" "B \<in> h" "X \<in> h"
  shows "X \<in> line A B"
proof-
  from `h \<in> HalfLine` have "\<exists>H C. h = halfline C H \<and> H \<noteq> C" by (subst(asm) halfline_distinct_def)
  then obtain H C where "h = halfline C H" and  "H \<noteq> C" by blast
  show "X \<in> line A B"
  proof (cases "A=C")
    assume "A\<noteq>C"
    from `A \<in> h` have "A \<in> halfline C H" by (subst(asm) `h = halfline C H`)
    from `A\<noteq>C` this have "h= halfline C A" by (subst `h = halfline C H`,
 rule_tac halfline_independence)
    from `A\<noteq>C` have halflineCA_def:"halfline C A = {P. \<not> between A C P \<and> P \<in> line C A}" 
      using halfline_def by simp
    from `X \<in> h` this have "X \<in> line C A" by (subst(asm) `h= halfline C A`, blast)
    from `B \<in> h` halflineCA_def have "B \<in> line C A" by (subst(asm) `h= halfline C A`, blast)
    from this `A \<noteq> B` have "line C A = line A B" 
      by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
    from `X \<in> line C A` show "X \<in> line A B" by (subst(asm) `line C A = line A B`)
  next
    assume "A=C"
    from `A \<noteq> B` have "C \<noteq> B" by (subst(asm) `A=C`)
    from `B \<in> h` have "B \<in> halfline C H" by (subst(asm) `h = halfline C H`)
    from `C\<noteq>B`[symmetric] this have "h= halfline C B" by (subst `h = halfline C H`, 
rule_tac halfline_independence)
    from `C\<noteq>B`[symmetric] have halflineCB_def:"halfline C B = {P. \<not> between B C P \<and> P \<in> line C B}"
      using halfline_def by simp
    from `X \<in> h` this have "X \<in> line C B" by (subst(asm) `h= halfline C B`, blast)
    from `A \<in> h` halflineCB_def have "A \<in> line C B" by (subst(asm) `h= halfline C B`, blast)
    from this `A \<noteq> B` have "line C B = line A B" 
      by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
    from `X \<in> line C B` show "X \<in> line A B" by (subst(asm) `line C B = line A B`)    
  qed
qed


lemma HalfLine_propersubset: assumes "h \<in> HalfLine" "l \<in> Line" "A \<in> h" 
"B \<in> h" "A \<in> l" "B \<in> l" "A \<noteq> B" 
                               shows "h \<subset> l"
proof -
  from `h \<in> HalfLine` have "\<exists>H X. h = halfline X H \<and> H \<noteq> X" by (subst(asm) halfline_distinct_def)
  then obtain H X where "h = halfline X H" and  "H \<noteq> X" by blast
  have "X \<in> h" by (subst `h= halfline X H`, rule halfline_bestdef)
  from this assms have "X \<in> line A B" by (rule_tac halfline_points_on_line)
  have "h \<subset> line A B"
  proof (cases "A=X")
    assume "A\<noteq>X"
    from `A \<in> h` have "A \<in> halfline X H" by (subst(asm) `h = halfline X H`)
    from `A\<noteq>X` this  have "h= halfline X A" 
      by (subst `h = halfline X H`, rule_tac halfline_independence)
    have "h \<subset> line X A" by (subst `h= halfline X A`, rule halfline_propersubset)
    from `X \<in> line A B` `A\<noteq>X`[symmetric] have "line A B = line X A"
      by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
    from `h \<subset> line X A` show "h \<subset> line A B" by (subst(asm) `line A B = line X A`[symmetric])
  next
    assume "A=X"
    from `A \<noteq> B` have "X \<noteq> B" by (subst(asm) `A=X`)
    from `B \<in> h` have "B \<in> halfline X H" by (subst(asm) `h = halfline X H`)
    from `X\<noteq>B`[symmetric] this  have "h= halfline X B" 
      by (subst `h = halfline X H`, rule_tac halfline_independence)
    have "h \<subset> line X B" by (subst `h= halfline X B`, rule halfline_propersubset)
    from `X \<in> line A B` `B\<noteq>X`[symmetric] have "line A B = line X B"
      by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
    from `h \<subset> line X B` show "h \<subset> line A B" by (subst(asm) `line A B = line X B`[symmetric])
  qed
  from assms(2,5,6,7) have "l = line A B" by (rule line_bestdef_inv)
  from `h \<subset> line A B` show "h \<subset> l" by (subst(asm) `l = line A B`[symmetric])
qed

lemma unique_line_halfline: assumes "h \<in> HalfLine" shows "\<exists>!l \<in> Line. h \<subseteq> l"
proof -
  from assms obtain X A where h_def:"h = halfline X A" "A \<noteq> X" using halfline_distinct_def by blast
  then have "h \<subseteq> line X A" using halfline_propersubset by blast
  {fix l
  assume "l \<in> Line" "h \<subseteq> l"
  have "A \<in> l" "X \<in> l" using `h \<subseteq> l` halfline_bestdef h_def by blast+
  from this `l \<in> Line` line_bestdef `A \<noteq> X` have "l = line X A" using line_bestdef_inv by blast}
  from this `h \<subseteq> line X A` show ?thesis
    using line_bestdef(1) by blast
qed

definition "endpoint h = (THE X. \<exists> A. h = halfline X A)"

lemma endpoint_bestdef: assumes "h \<in> HalfLine" shows "\<exists> A. h = halfline (endpoint h) A"
proof (subst endpoint_def, rule theI')
  from assms obtain X A where A_def:"h = halfline X A \<and> A \<noteq> X" using halfline_distinct_def by blast
  then have exists: "\<exists>X. \<exists>A. h = halfline X A" by blast
  have unique: "\<forall>Y. (\<exists>B. h = halfline Y B) \<longrightarrow> X=Y"
  proof (rule allI, rule impI)
    fix Y
    assume "\<exists>B. h = halfline Y B"
    show "X = Y"
    proof (rule ccontr)
      assume "X \<noteq> Y"
      from `\<exists>A. h = halfline Y A` have "Y \<in> h" using halfline_bestdef by fast
      from this `X \<noteq> Y` A_def have "h = halfline X Y" using halfline_independence by blast
      from `\<exists>B. h = halfline Y B` obtain B where B_def: "h = halfline Y B" by (rule exE)
      from A_def have "X \<in> h" using  halfline_bestdef by fast
      from this `X \<noteq> Y` B_def have "h = halfline Y X" using halfline_independence by blast
      from `h = halfline Y X` have "halfline X Y = halfline Y X" by (subst(asm) `h = halfline X Y`)
      have "line X Y \<in> Line" by (rule line_bestdef)
      then obtain x where x_def:"x\<in>Coord (line X Y)" by (rule_tac exE,rule  brossard_line_measure1)
      from `X \<noteq> Y` this line_bestdef coordfn_preserves_distinctness 
      consider "x X < x Y"| "x Y < x X" 
        by fastforce
      then show False
      proof (cases)
        assume "x X < x Y"
        from `line X Y \<in> Line` x_def have "\<exists>P \<in> (line X Y). x P = x X - 1" by (rule ex_pt_for_real)
        then obtain P where "P \<in> line X Y" and "x P = x X - 1" by (rule bexE)
        then have "x P < x X" by simp
        from this `x X < x Y` x_def line_bestdef have "P \<noteq> Y" using coordfn_preserves_distinctness
          by force
        from `x P < x X` `x X < x Y` x_def have "\<not> between X Y P" using between_expanded_def
          by simp
        from this `P \<noteq> Y` `X \<noteq> Y` `P \<in> line X Y` line_sym have "P \<in> halfline Y X" 
          using halfline_def by auto
        from `P \<in> line X Y` `x P < x X` `x X < x Y` x_def line_sym have "between Y X P" 
          using between_expanded_def by auto
        from this `X \<noteq> Y` have "P \<notin> halfline X Y" using halfline_def by auto
        from this `P \<in> halfline Y X` `halfline X Y = halfline Y X` show False by auto
      next
        assume "x Y < x X"
        from `line X Y \<in> Line` x_def have "\<exists>P \<in> (line X Y). x P = x Y - 1" by (rule ex_pt_for_real)
        then obtain P where "P \<in> line X Y" and "x P = x Y - 1" by (rule bexE)
        then have "x Y > x P" by simp
        from this `x Y < x X` x_def line_bestdef have "P \<noteq> Y" 
          using coordfn_preserves_distinctness by force
        from `x Y > x P` `x Y < x X` x_def line_sym have "\<not> between Y X P" 
          using between_expanded_def by simp
        from this `P \<noteq> Y` `X \<noteq> Y` `P \<in> line X Y` line_sym have "P \<in> halfline X Y" 
          using halfline_def by auto
        from `P \<in> line X Y` `x Y > x P` `x Y < x X` x_def line_sym have "between X Y P" 
          using between_expanded_def by auto
        from this `X \<noteq> Y` have "P \<notin> halfline Y X" using halfline_def by auto
        from this `P \<in> halfline X Y` `halfline X Y = halfline Y X` show False by auto
      qed
    qed
  qed
  from exists unique show "\<exists>!x. \<exists>A. h = halfline x A" by metis
qed

lemma unique_endpoint: assumes "\<exists>A. h = halfline X A" shows "X = (endpoint h)"
proof (rule ccontr)
  define Y where "Y = (endpoint h)"
  assume "X \<noteq> (endpoint h)"
  from this Y_def have "X \<noteq> Y" by simp
  from assms(1) have "h \<in> HalfLine" using halfline_bestdef by blast
  from this have "\<exists>A. h = halfline Y A" by (subst Y_def, rule endpoint_bestdef)
  from assms obtain A where A_def: " h = halfline X A" by (rule exE)
  from `\<exists>A. h = halfline Y A` have "Y \<in> h" using halfline_bestdef by fast
  from this `X \<noteq> Y` A_def have "h = halfline X Y" using halfline_independence by blast
  from `\<exists>B. h = halfline Y B` obtain B where B_def: "h = halfline Y B" by (rule exE)
  from A_def have "X \<in> h" using  halfline_bestdef by fast
  from this `X \<noteq> Y` B_def have "h = halfline Y X" using halfline_independence by blast
  from `h = halfline Y X` have "halfline X Y = halfline Y X" by (subst(asm) `h = halfline X Y`)
  have "line X Y \<in> Line" by (rule line_bestdef)
  then obtain x where x_def:"x\<in>Coord (line X Y)" by (rule_tac exE,rule  brossard_line_measure1)
  from `X \<noteq> Y` this line_bestdef coordfn_preserves_distinctness consider "x X < x Y"| "x Y < x X" 
    by fastforce
  then show False
  proof (cases)
    assume "x X < x Y"
    from `line X Y \<in> Line` x_def have "\<exists>P \<in> (line X Y). x P = x X - 1" by (rule ex_pt_for_real)
    then obtain P where "P \<in> line X Y" and "x P = x X - 1" by (rule bexE)
    then have "x P < x X" by simp
    from this `x X < x Y` x_def line_bestdef have "P \<noteq> Y" using coordfn_preserves_distinctness
      by force
    from `x P < x X` `x X < x Y` x_def have "\<not> between X Y P" using between_expanded_def by simp
    from this `P \<noteq> Y` `X \<noteq> Y` `P \<in> line X Y` line_sym have "P \<in> halfline Y X" using halfline_def
      by auto
    from `P \<in> line X Y` `x P < x X` `x X < x Y` x_def line_sym have "between Y X P" 
      using between_expanded_def by auto
    from this `X \<noteq> Y` have "P \<notin> halfline X Y" using halfline_def by auto
    from this `P \<in> halfline Y X` `halfline X Y = halfline Y X` show False by auto
  next
    assume "x Y < x X"
    from `line X Y \<in> Line` x_def have "\<exists>P \<in> (line X Y). x P = x Y - 1" by (rule ex_pt_for_real)
    then obtain P where "P \<in> line X Y" and "x P = x Y - 1" by (rule bexE)
    then have "x Y > x P" by simp
    from this `x Y < x X` x_def line_bestdef have "P \<noteq> Y" 
      using coordfn_preserves_distinctness by force
    from `x Y > x P` `x Y < x X` x_def line_sym have "\<not> between Y X P" 
      using between_expanded_def by simp
    from this `P \<noteq> Y` `X \<noteq> Y` `P \<in> line X Y` line_sym have "P \<in> halfline X Y"
      using halfline_def by auto
    from `P \<in> line X Y` `x Y > x P` `x Y < x X` x_def line_sym have "between X Y P" 
      using between_expanded_def by auto
    from this `X \<noteq> Y` have "P \<notin> halfline Y X" using halfline_def by auto
    from this `P \<in> halfline X Y` `halfline X Y = halfline Y X` show False by auto
  qed
qed



lemma endpoint_agrees: shows "endpoint(halfline X A) = X"
  using unique_endpoint by metis

lemma endpoint_halfline_def:
  shows "(g \<in> HalfLine) = (\<exists> A. g = halfline (endpoint g) A \<and> A \<noteq> (endpoint g))"
proof
  assume "g \<in> HalfLine"
  then have "\<exists>A X. g = halfline X A \<and> A \<noteq> X" by (subst(asm) halfline_distinct_def)
  then obtain A X where AX_def: "g = halfline X A" "A \<noteq> X" by blast
(* obtain A X where "g = halfline X A \<and> A \<noteq> X" by (drule_tac exE, rule_tac exE)*)
  have "(endpoint g) = X" by (subst `g = halfline X A`, rule endpoint_agrees)
  from this AX_def show "\<exists>A. g = halfline (endpoint g) A \<and> A \<noteq> (endpoint g)" by blast
next
  assume "\<exists>A. g = halfline (endpoint g) A \<and> A \<noteq> (endpoint g)"
  then have "\<exists>A X. g = halfline X A \<and> A \<noteq> X" by (subst ex_comm, rule_tac exI)
  then show "g \<in> HalfLine" by (subst halfline_distinct_def)
qed

lemma halflineXA_distinct_def: shows "\<exists>B. halfline X A = halfline X B \<and> B \<noteq> X"
  using endpoint_halfline_def endpoint_agrees halfline_bestdef by presburger

lemma  halfline_independence_converse: assumes "halfline X A = halfline X B"
  shows "B \<in> halfline X A"
proof -
  have "B \<in> halfline X B" by (rule halfline_bestdef)
  then show ?thesis by (subst `halfline X A = halfline X B`)
qed

lemma halfline_independence_inv: assumes "B \<notin> line X A"
  shows "halfline X A \<noteq> halfline X B"
proof -
  from halflineXA_distinct_def obtain C where "C \<noteq> X" and "halfline X A = halfline X C" by blast
  from halflineXA_distinct_def obtain D where "D \<noteq> X" and "halfline X B = halfline X D" by blast
  have "halfline X C \<noteq> halfline X D"
  proof (rule ccontr, drule notnotD,drule_tac halfline_independence_converse)
    assume "D \<in> halfline X C"
    from `C \<noteq> X` this have "D \<in> line X C" using halfline_def by auto
    have "X \<in> line X A" by (rule line_bestdef)
    have "C \<in> halfline X C" by (rule halfline_bestdef)
    from this have "C \<in> line X A" using halfline_propersubset `halfline X A = halfline X C` 
      by blast
    from `X \<in> line X A` `C \<in> line X A` `C \<noteq> X`[symmetric]
    have "line X A = line X C" by (rule_tac line_bestdef_inv, rule_tac line_bestdef)
    from `D \<in> line X C` have "D \<in> line X A" by (subst `line X A = line X C`)
    have "D \<in> halfline X D" by (rule halfline_bestdef)
    from this have "D \<in> line X B" using halfline_propersubset `halfline X B = halfline X D` 
      by blast    
    from this `D \<in> line X A` have "B \<in> line X A"
      using \<open>D \<noteq> X\<close> not_on_line_sym same_line by blast
    from this assms show False by contradiction
  qed
  from this show ?thesis by (subst `halfline X A = halfline X C`,
 subst `halfline X B = halfline X D`)
qed

lemma endpoint_in_halfline: assumes "g \<in> HalfLine" shows "(endpoint g) \<in> g" 
proof -
  from assms obtain A where "g = halfline (endpoint g) A" "A \<noteq> endpoint g"
    using endpoint_halfline_def by auto
  show "(endpoint g) \<in> g" by (subst(2) `g = halfline (endpoint g) A`, rule_tac halfline_bestdef)
qed 

lemma edgepoint_imp_notbetween: assumes "between A B C" shows "(\<not> between B A C)"
proof (rule ccontr, drule notnotD)
  assume "between B A C"
  have "line A B \<in> Line" by (rule line_bestdef)
  then obtain x where x_def: "x\<in>Coord (line A B)" by (rule_tac exE,rule  brossard_line_measure1)
  from this `between A B C` have a: "x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A"
    using between_expanded_def by metis
  from `x\<in>Coord (line A B)` have "x\<in>Coord (line B A)" by (subst line_sym)
  from this `between B A C` have b: "x B < x A \<and> x A < x C \<or> x C < x A \<and> x A < x B"
    using between_expanded_def by metis 
  from a b show False by linarith
qed

lemma notbetween_imp_edgepoint: assumes "C \<in> line A B" "A\<noteq>B" "B\<noteq>C" "C\<noteq>A" "\<not> between B A C"
                                   shows "between A B C \<or> between A C B"
proof -
  have "line A B \<in> Line" by (rule line_bestdef)
  then obtain x where x_def: "x\<in>Coord (line A B)" by (rule_tac exE,rule  brossard_line_measure1)
  from `B\<noteq>C` `C \<in> line A B` have "line A B = line B C" 
    by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
  from `C\<noteq>A` `C \<in> line A B` have "line A B = line C A" 
    by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
  from `A\<noteq>B`  x_def have "x A\<noteq>x B" using  line_bestdef coordfn_preserves_distinctness
    by blast
  from `B\<noteq>C` x_def have "x B\<noteq>x C" using  line_bestdef coordfn_preserves_distinctness
    by (subst(asm) `line A B = line B C`, blast)
  from `C\<noteq>A` x_def have "x C\<noteq>x A" using  line_bestdef coordfn_preserves_distinctness
    by (subst(asm) `line A B = line C A`, blast)
  have "B\<in> line A C" by (subst line_sym, subst `line A B = line C A`[symmetric], rule line_bestdef)
  from x_def have x_def':"x\<in>Coord (line A C)" by (subst line_sym, subst(asm) `line A B = line C A`)
  from `\<not> between B A C` x_def 
  have "C \<notin> line B A \<or> \<not>(x B < x A \<and> x A < x C \<or> x C < x A \<and> x A < x B)" 
    using between_expanded_def by (subst(asm) line_sym, force)
  from this `C \<in> line A B` have "\<not>(x B < x A \<and> x A < x C \<or> x C < x A \<and> x A < x B)"
    by (subst(asm) line_sym, safe) 
  from this have "(\<not>(x B < x A) \<or> \<not>(x A < x C)) \<and> (\<not>(x C < x A) \<or> \<not>(x A < x B))"
    by blast
  from this `x A\<noteq>x B` `x B\<noteq>x C` `x C\<noteq>x A` have "(x A < x B \<or> x C < x A) \<and> (x A < x C \<or> x B < x A)"
    by linarith
  from this `x B\<noteq>x C` have "(x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A) \<or>
                        (x A < x C \<and> x C < x B \<or> x B < x C \<and> x C < x A)" by linarith
  moreover from x_def `C \<in> line A B`
  have "between A B C = (x A < x B \<and> x B < x C \<or> x C < x B \<and> x B < x A)"
    using between_expanded_def by force
  moreover from x_def' `B \<in> line A C` 
  have "between A C B = (x A < x C \<and> x C < x B \<or> x B < x C \<and> x C < x A)"
    using between_expanded_def by force
  ultimately show "between A B C \<or> between A C B" by blast
qed

lemma between_imp_eq_halflines: assumes "between X A P" shows "halfline X A = halfline X P"
proof -
  have "line X A \<in> Line" by (rule line_bestdef)
  then obtain x where x_def: "x\<in>Coord (line X A)" by (rule_tac exE,rule  brossard_line_measure1)
  from this assms have betXAP:"x X < x A \<and> x A < x P \<or> x P < x A \<and> x A < x X" and "P \<in> line X A" 
    using between_expanded_def by (metis, rule_tac between_imp_collinear)
  from `between X A P` have "X \<noteq> A" and "X \<noteq> P" using bet_imp_distinct by (blast, blast)
  from this have halflineXA:"halfline X A = {Q. \<not> between A X Q \<and> Q \<in> line X A}"
             and halflineXP:"halfline X P = {Q. \<not> between P X Q \<and> Q \<in> line X P}" 
    using halfline_def by (force, force)
  from `P \<in> line X A` `X \<noteq> P` have "line X A = line X P" 
    by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
  from x_def have x_defPX:"x \<in> Coord (line P X)" 
    by (subst(asm) `line X A = line X P`, subst(asm) line_sym)
  from x_def have x_defAX:"x \<in> Coord (line A X)" by (subst(asm) line_sym)
  have "\<forall>Q. between A X Q = between P X Q"
  proof (rule allI, rule iffI)
    fix Q
    assume "between A X Q"
    from x_defAX `between A X Q` have "x A < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x A"
 and "Q \<in> line A X" 
      by (rule_tac [!] between_true)
    then consider "x A < x X \<and> x X < x Q"| "x Q < x X \<and> x X < x A" by fast
    then have "x P < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x P"
    proof (cases)
      assume "x A < x X \<and> x X < x Q"
      from this betXAP have "x P < x A \<and> x A < x X" by linarith
      from this `x A < x X \<and> x X < x Q` have "x P < x X \<and> x X < x Q" by linarith
      then show "x P < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x P" by linarith 
    next
      assume "x Q < x X \<and> x X < x A"
      from this betXAP have "x X < x A \<and> x A < x P" by linarith
      from this `x Q < x X \<and> x X < x A` have "x Q < x X \<and> x X < x P" by linarith
      then show "x P < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x P" by linarith  
    qed
    from `Q \<in> line A X` have "Q \<in> line P X" 
      by (subst line_sym, subst `line X A = line X P`[symmetric], subst(asm) line_sym)
    from this `x P < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x P` x_def 
    show "between P X Q" using between_expanded_def
      by (subst(asm) `line X A = line X P`, subst(asm)(2) line_sym, metis)
  next
    fix Q
    assume "between P X Q"
    from `between P X Q` x_defPX 
    have "x P < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x P" "Q \<in> line P X" 
      by (rule_tac [!] between_true)
    then consider "x P < x X \<and> x X < x Q"| "x Q < x X \<and> x X < x P" by fast
    then have "x A < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x A"
    proof (cases)
      assume "x P < x X \<and> x X < x Q"
      from this betXAP have "x P < x A \<and> x A < x X" by linarith
      from this `x P < x X \<and> x X < x Q` have "x A < x X \<and> x X < x Q" by linarith
      then show "x A < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x A" by linarith 
    next
      assume "x Q < x X \<and> x X < x P"
      from this betXAP have "x X < x A \<and> x A < x P" by linarith
      from this `x Q < x X \<and> x X < x P` have "x Q < x X \<and> x X < x A" by linarith
      then show "x A < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x A" by linarith  
    qed
    from `Q \<in> line P X` have "Q \<in> line A X" 
      by (subst line_sym, subst `line X A = line X P`, subst(asm) line_sym)
    from this `x A < x X \<and> x X < x Q \<or> x Q < x X \<and> x X < x A` x_def 
    show "between A X Q" using between_expanded_def
      by (subst(asm)(2) line_sym, metis)
  qed
  from this `line X A = line X P` halflineXA halflineXP show "halfline X A = halfline X P"
    by presburger
qed

lemma sameside_imp_eq_halflines: assumes "sameside A P X" shows "halfline X A = halfline X P"
proof (insert assms, subst(asm) sameside_def)
  assume "between X P A \<or> between X A P"
  then consider "between X P A" | " between X A P" by auto
  then show ?thesis 
  proof (cases)
    assume "between X P A"
    then show "halfline X A = halfline X P" by (rule between_imp_eq_halflines[symmetric])
  next
    assume " between X A P"
    then show "halfline X A = halfline X P" by (rule between_imp_eq_halflines)
  qed
qed


lemma unionI: "(x \<notin> A \<Longrightarrow> x \<in> B) \<Longrightarrow> x \<in> A \<union> B"
  by auto


lemma line_built_from_halflines: assumes "between A X P"
      shows "line A P = halfline X A \<union> halfline X P"
proof (rule equalityI, rule subsetI)
  from assms have "P \<in> line A X" by (rule between_imp_collinear) 
  have "X \<in> line A X" by (rule line_bestdef)
  from assms have "A\<noteq>X" "X\<noteq>P" "A\<noteq>P"by (rule_tac [!] bet_imp_distinct)
  from `A\<noteq>P` `P\<in>line A X` have "line A X = line A P"
    by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
  from `X \<in> line A X` have "X \<in> line A P" by (subst(asm) `line A X = line A P`)
  have XA:"halfline X A \<subset> line X A" by (rule halfline_propersubset)
  have XP:"halfline X P \<subset> line X P" by (rule halfline_propersubset)
  from `X \<in> line A P` `A\<noteq>X`[symmetric] have "line A P = line X A" 
    by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
    from `X \<in> line A P` `X\<noteq>P` have "line A P = line X P" 
      by (rule_tac line_bestdef_inv, frule_tac [!] line_bestdef)
    from XA XP show "halfline X A \<union> halfline X P \<subseteq> line A P"
      by (subst(asm) `line A P = line X A`[symmetric],
          subst(asm) `line A P = line X P`[symmetric], auto)
  fix Q
  assume "Q \<in> line A P"
  show "Q \<in> halfline X A \<union> halfline X P "
  proof (rule unionI)
    assume "Q \<notin> halfline X A"
    from `Q \<in> line A P` have "Q \<in> line X A" by (subst(asm) `line A P = line X A`)
    from `X \<noteq> A` `Q \<notin> halfline X A` this have "between A X Q" using halfline_def by simp
    from `Q \<in> line A P` have "Q \<in> line X P" by (subst(asm) `line A P = line X P`)
    from `between A X P` `between A X Q` have "\<not>between P X Q" by (rule sameside_eq_notbetween)
    from `X\<noteq>P` this `Q \<in> line X P` show "Q \<in> halfline X P" using halfline_def by simp
  qed
qed

definition
 "otherhalf h = (THE g. g\<in>HalfLine \<and> (endpoint h) = endpoint g \<and> (\<exists>l \<in> Line. g \<union> h = l))"

lemma otherhalf_bestdef: assumes "h \<in> HalfLine" 
  shows "(endpoint h) = endpoint (otherhalf h)" "\<exists>l \<in> Line. (otherhalf h) \<union> h = l" 
"(otherhalf h) \<in> HalfLine"
proof -
  (*constructing points on h so we can talk about the line which h is on*)
  from assms have "\<exists>A X. h = halfline X A \<and> A \<noteq> X" 
    by (subst(asm) HalfLine_bestdef, subst(asm) halfline_distinct_def)
  then obtain A X where h_def: "h = halfline X A" and "A \<noteq> X" by blast
  then have "A \<in>halfline X A" and "X \<in> halfline X A" using halfline_bestdef by (blast, blast)
  from h_def `h \<in> HalfLine` have "X = endpoint h" using unique_endpoint by blast
  have "line X A \<in> Line" by (rule line_bestdef)
  have "halfline X A \<subset> line X A" by (rule halfline_propersubset)
  (*constructing a witness to show there exists such a halfline*)
  from `A \<noteq> X` obtain B where "B\<in>line X A" and "between A X B" 
    by (frule_tac between_otherside, rule_tac bexE)
  from `between A X B` have "X \<noteq> B" using bet_imp_distinct by blast
  have "halfline X B \<in> HalfLine" by (rule halfline_bestdef)
  from `B\<in>line X A` `X \<noteq> B` have "line X A = line X B" 
    by (rule_tac line_bestdef_inv, auto simp: line_bestdef)
  from `A \<noteq> X` have halflineXA_def:"halfline X A = {P. \<not> between A X P \<and> P \<in> line X A}" 
    using halfline_def
      by simp
  (*showing the witness satisfies the properties*)
  have "halfline X B \<subset> line X A" by (subst `line X A = line X B`, rule halfline_propersubset)
  from `X \<noteq> B` have halflineXB_def: "halfline X B = {P. \<not> between B X P \<and> P \<in> line X B}" 
    using halfline_def
    by simp
  have "line X A \<subseteq> halfline X B \<union> halfline X A"
  proof safe
    fix P
    assume "P \<in> line X A"
    assume "P \<notin> halfline X A"
    from halflineXA_def `P \<in> line X A` `P \<notin> halfline X A` have "between A X P" by blast
    from `between A X B` this have "\<not>between B X P" by (rule sameside_eq_notbetween)
    from halflineXB_def `\<not>between B X P` `line X A = line X B` `P \<in> line X A` 
    show "P \<in> halfline X B" 
      by blast
  qed
  from this `halfline X B \<subset> line X A` `halfline X A \<subset> line X A`
  have union: "halfline X B \<union> halfline X A = line X A" by blast
  have endpointXB: "(endpoint h) = endpoint (halfline X B)" using `halfline X B \<in> HalfLine` 
 endpoint_bestdef unique_endpoint
    by (subst `X = endpoint h`[symmetric], metis)
  have "(otherhalf h)\<in>HalfLine 
\<and> (endpoint h) = endpoint (otherhalf h) \<and> (\<exists>l \<in> Line. (otherhalf h) \<union> h = l)"
  proof (subst otherhalf_def, subst otherhalf_def, subst otherhalf_def, rule theI')
    from union endpointXB h_def `line X A \<in> Line` `halfline X B \<in>HalfLine`
    have exists:"\<exists>x. x\<in>HalfLine\<and>(endpoint h) = endpoint x \<and> (\<exists>l \<in> Line. x \<union> h = l)" by blast
 (*now we assume that there is another halfline with same properties in order to show uniqueness*)
    have "\<forall> oth . oth\<in>HalfLine \<longrightarrow> 
(endpoint h) = endpoint oth \<longrightarrow> (\<exists>l \<in> Line. oth \<union> h = l) \<longrightarrow> oth = halfline X B"
    proof (rule allI, rule impI, rule impI, rule impI)
      fix oth
      assume "oth\<in>HalfLine"
      assume "(endpoint h) = endpoint oth" 
      from `oth\<in>HalfLine` have "\<exists>A. oth = halfline (endpoint oth) A" by (rule endpoint_bestdef)
      from this have "\<exists>A. oth = halfline X A" by (subst `X = endpoint h`,
 subst `(endpoint h) = endpoint oth`)
      from this obtain C where oth_def: "oth = halfline X C" by (rule exE)
      assume "\<exists>l \<in> Line. oth \<union> h = l"
      then obtain l where "l \<in> Line" "oth \<union> h = l" by (rule bexE)
      from `h = halfline X A` `A \<in>halfline X A` `X \<in> halfline X A` `oth \<union> h = l`
      have "A \<in> l" "X \<in> l"
        by (fast, fast)
      have "A \<in>line A X" "X \<in> line A X" "line A X \<in> Line" by (rule_tac [!] line_bestdef) 
      from this `A \<in> l` `X \<in> l` `l \<in> Line` `A \<noteq> X` have "l = line A X" 
        using point_line_brossard_line2' by auto
      from `halfline X A \<subset> line X A` have "\<exists>x \<in> line X A. x \<notin> halfline X A" by blast
      then obtain P where "P \<in> line X A"  "P \<notin> halfline X A" by (rule bexE)
      from `P \<in> line X A` `oth \<union> h = l` have "P \<in> oth \<or> P \<in> h" using line_sym
        by (subst(asm) `l = line A X`, auto)
      from this `P \<notin> halfline X A` `h = halfline X A` have "P \<in> oth" by simp
      from `P \<in> line X A` halflineXA_def `P \<notin> halfline X A` have "between A X P" by blast
      from this `between A X B` have "\<not> between P X B" by (rule sameside_eq_notbetween)
      from `X \<in> halfline X A` `P \<notin> halfline X A` have "P \<noteq> X" by blast
      have "line X P \<in> Line" "X \<in> line X P" "P \<in>line X P" by (rule_tac [!] line_bestdef)
      from `P \<in>line X P` `X \<in> line X P` `line A X \<in> Line` `P \<in> line X A` 
`X \<in> line A X` `line X P \<in> Line` `P \<noteq> X`
      have "line X A = line P X" using point_line_brossard_line2' line_sym by blast
      from `P \<noteq> X` halfline_def have halflineXP_def:
 "halfline X P  = {Q. \<not> between P X Q \<and> Q \<in> line X P}"
        by force
      from `line X A = line P X` `B \<in> line X A` have "B \<in> line X P" using line_sym by blast
      from halflineXP_def this `\<not> between P X B` have "B \<in> halfline X P" by blast
      from this `X \<noteq> B`[symmetric] have "halfline X P = halfline X B" 
        by (rule halfline_independence)
      from `P \<in> oth` have "P \<in> halfline X C" by (subst(asm) `oth = halfline X C`)
      from this `P \<noteq> X` have "halfline X C = halfline X P" by (rule halfline_independence)
      from this `halfline X P = halfline X B` show "oth = halfline X B"
        by (subst `oth = halfline X C`, rule trans)
    qed
    from this exists
    show "\<exists>!x. x\<in>HalfLine \<and> (endpoint h) = endpoint x \<and> (\<exists>l \<in> Line. x \<union> h = l)" by blast
  qed
  then show "(otherhalf h) \<in>HalfLine" "(endpoint h) = endpoint (otherhalf h)"
 "(\<exists>l\<in>Line. otherhalf h \<union> h = l)" 
    by auto
qed

end 

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
  also have 3: "... = bundle h g" by (subst bundle_def, rule refl)
  finally show "bundle g h = bundle h g" using 1 2 3 by blast
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
          from this E_def abs_real_def have "\<epsilon>2 = -1" sledgehammer

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