theory Metric_Geometry imports Main Real Mod4

begin

(*prove Birkhoff's corollary of the axiom of continuity, and then prove Brossard's axiom of
 continuity*)

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

lemma line_through_point: "\<exists> l \<in> Line. (A::'p) \<in> l"
proof -
 have  "\<exists> l. isLine l \<and> (A::'p) \<in> l" by (metis second_point point_line_brossard_line2)
 then show ?thesis using Line_def by simp
qed


definition "line A B == (if A \<noteq> B then THE l. isLine l \<and> A \<in> l \<and> B \<in> l 
                     else SOME l. isLine l \<and> A \<in> l)"

lemma unique_line: assumes "A \<noteq> B"  shows "isLine (line A B)"
                         and "A \<in> (line A B)" and "B \<in> (line A B)"
proof -
  from `A \<noteq> B` have new_line_def:  "line A B = (THE l. isLine l \<and> A \<in> l \<and> B \<in> l)" by (simp add: line_def)
  from `A \<noteq> B` have "\<exists>!l. isLine l \<and> A \<in> l \<and> B \<in> l" by (rule point_line_brossard_line2)
  then have "isLine (line A B) \<and> A \<in> (line A B) \<and> B \<in> (line A B)"
    by (subst new_line_def,subst new_line_def,subst new_line_def, rule theI')
  then show "isLine (line A B)" and "A \<in> (line A B)" and "B \<in> (line A B)" by auto 
qed

lemma line_bestdef:    shows "(line A B) \<in> Line"
                         and "A \<in> (line A B)" and "B \<in> (line A B)"
  proof (case_tac [!] "A=B")
    assume "A\<noteq>B"
    then have "isLine (line A B)" and "A \<in> (line A B)" and "B \<in> (line A B)" by (rule_tac [!] unique_line)
    then show "(line A B) \<in> Line" and "A \<in> (line A B)" and "B \<in> (line A B)" using Line_def by auto
    next
    assume "A=B"
    then have new_line_def:  "line A B = (SOME l. isLine l \<and> A \<in> l)" by (simp add: line_def)
    obtain C where "C\<noteq>A" using second_point by fastforce
    then have "isLine (line A C) \<and> A \<in> (line A C)" by (simp add: unique_line)
    then have "\<exists> l. isLine l \<and> A \<in> l" by auto
    then have "isLine (line A B) \<and> A \<in> (line A B)" by (subst new_line_def, subst new_line_def, rule someI_ex)
    then have "isLine (line A B)"  and "A \<in> (line A B)" by auto
    then show "(line A B) \<in> Line"  and "A \<in> (line A B)" using Line_def by auto
    then show "B \<in> (line A B)" using `A = B`  by auto
  qed

definition "collinear A B C == (C \<in> line A B \<or> A = B)" 
(*This definition is wrong for the case A=B because the arbitrary line chosen might not include C
even if it could. We could define a lines through point set and have hilbert choice pick us one in 
definition of line A B? Could we let it be a set ...? Then previous proof wouldn't work at least.*)

lemma line_bestdef_inv: assumes "l \<in> Line" and "A \<in> l" and "B \<in> l" and  "A\<noteq>B"
                          shows "l = (line A B)" 
proof -
  from `A\<noteq>B` have "\<exists>!l \<in> Line. A \<in> l \<and> B \<in> l" by (rule point_line_brossard_line2')
  moreover have "(line A B) \<in> Line \<and> A \<in> (line A B) \<and> B \<in> (line A B)" by (simp only: line_bestdef)
  moreover have "l \<in> Line\<and> A \<in> l\<and> B \<in> l" by (simp only: assms(1,2,3))
  ultimately show ?thesis by blast
qed

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

end

locale Line_Measure = Lines isLine
  for isLine ::"'p set \<Rightarrow> bool" +
  fixes coord  :: "'p set \<Rightarrow> 'p  \<Rightarrow> real" 
  fixes d :: "'p \<Rightarrow> 'p \<Rightarrow> real"
  assumes
  coord_bij: "l \<in> Line \<Longrightarrow> bij_betw (coord l) l (UNIV::real set)"
  and line_measure: "\<lbrakk>l \<in> Line; A \<in> l; B \<in> l\<rbrakk> \<Longrightarrow> \<bar>coord l A - coord l B\<bar> = d A B"
context Line_Measure
begin
(*also show it is a metric?*)
lemma d_symmetric: "d A B = d B A" and d_nonneg: "d A B \<ge>0" and d_posdef: "(d A B = 0) \<longleftrightarrow> (A = B)"
proof -
  have "line A B \<in> Line" and "A \<in> line A B" and "B \<in> line A B" by (rule_tac [!] line_bestdef)
  then have d_def:"d A B = \<bar>coord (line A B) A - coord (line A B) B\<bar>" by (rule line_measure[symmetric])
  also have "... = \<bar>coord (line A B) B - coord (line A B) A\<bar>" by simp
  finally show "d A B = d B A" using `line A B \<in> Line` `A \<in> line A B` `B \<in> line A B` line_measure
    by simp
  from d_def show "d A B \<ge>0" by simp
  show "(d A B = 0) \<longleftrightarrow> (A = B)"
  proof
    assume "A = B"
    from this d_def show "d A B = 0" by simp
  next
    assume "d A B = 0"
    from this d_def have "\<bar>coord (line A B) A - coord (line A B) B\<bar> = 0" by simp
    then have "coord (line A B) A = coord (line A B) B" by simp
    have "inj_on (coord (line A B)) (line A B)" 
      using `line A B \<in> Line` coord_bij bij_betw_def by blast
   from `coord (line A B) A = coord (line A B) B` this  show "A = B"
     by (simp add: `A \<in> line A B` `B \<in> line A B` inj_onD)  
   qed
qed

definition "ordered A B C == collinear A B C \<and> 
(((coord (line A B) A \<ge> coord (line A B) B) \<and> (coord (line A B) B \<ge> coord (line A B) B)) \<or> 
((coord (line A B) A \<le> coord (line A B) B) \<and> (coord (line A B) A \<le> coord (line A B) B)))"
 
definition " properly_ordered A B C == collinear A B C \<and> 
(((coord (line A B) A > coord (line A B) B) \<and> (coord (line A B) B > coord (line A B) B)) \<or> 
((coord (line A B) A < coord (line A B) B) \<and> (coord (line A B) A < coord (line A B) B)))"
(* Is it a good idea to define such things as properly ordered if we won't be using them much?*)
lemma line_equality: "ordered A B C \<Longrightarrow> d A C = d A B + d B C"
oops

lemma line_equality_iff: "collinear A B C \<Longrightarrow> (properly_ordered A B C) = 
(d A C = d A B + d B C \<and> \<not>(d A B = d A C + d C B) \<and> \<not>(d B C = d B A + d A C))"
  oops
(*what if they are all equal?*)
(*this is what Birkhoff says but it might not be worth proving*)
(*maybe collinearity assumption isn't needed or is put wrongly. 
Because (d A C = d A B + d B C) ought to imply it.*)

definition "between A B C == (d A C = d A B + d B C)"
lemma Lines_have_points: assumes "l \<in> Line" (*cannot be proven in Lines!
Can we prove it for any n? Perhaps inductively.*)
                           shows "\<exists> A B. A \<in> l \<and> B \<in> l \<and> A \<noteq> B"
  oops

lemma Unique_intersection: assumes "l \<in> Line" and "isline m" and "l\<noteq>m"
                             shows "\<exists>!X. X \<in> l \<and> X \<in> m"
oops
lemma Lines_are_dense:  assumes "l \<in> Line" 
                          shows  "A \<in>l \<and> B \<in> l \<Longrightarrow> \<exists>C. C \<in> l \<and> between A C B"
oops
definition "isSegment s == \<exists> A B. A \<noteq> B \<and> (\<forall>X. X\<in>s \<longleftrightarrow> (between A X B \<and> X \<in> (line A B)))"
definition "Segment == {s. isSegment s}"
definition "isHalfline h ==  \<exists> A G. A \<noteq> G \<and> (\<forall> X. X \<in> h  \<longleftrightarrow> (\<not> between A G X \<and> X \<in> (line A G)))"
definition "Halfline == {h. isHalfline h}"

definition "endpoint G h ==  \<exists> A. A \<noteq> G \<and> (\<forall> X. X \<in> h  \<longleftrightarrow> (\<not> between A G X \<and> X \<in> (line A G)))"

definition "A \<noteq> G \<Longrightarrow> en A G X == if coord (line A G) A < coord (line A G) G then coord (line A G) X - coord (line A G) G
else coord (line A G) G - coord (line A G) X"

lemma "(isHalfline h) = (\<exists> A G. h = {X. en A G X \<ge> 0})"
oops


lemma "\<forall>l \<in> Line. \<exists> h \<in> Halfline. \<exists> g \<in> Halfline. \<exists> X. l = h \<union> g "(*we can get disjoint union if we remove a point*)
oops

definition "R_mod4 == {q. 0 \<le> (q::real) \<and> q < 4}"
(*definition "R_mod4 == {q::real. \<exists>r::real. q = r mod 4}" but actually this is all the reals - they have 
cardinality anyway, so does it matter?*)
(*we have \<angle>*)

definition "Halflines G == {h. h\<in> Halfline \<and> endpoint G h}"
end

locale Angle_Measure = Line_Measure isLine coord d
  for isLine :: "'p set \<Rightarrow> bool" and coord:: "'p set \<Rightarrow> 'p  \<Rightarrow> real" and  d :: "'p \<Rightarrow> 'p \<Rightarrow> real" +
  fixes acoord :: "'p \<Rightarrow> 'p set \<Rightarrow> real"
  fixes  a :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" 
  assumes 
  acoord_bij: "bij_betw (acoord G) (Halflines G) R_mod4" 
  and angle_measure: "\<lbrakk>h \<in> Halfline; g \<in> Halfline;endpoint G h; endpoint G g; A \<in> h; B \<in> g\<rbrakk> 
\<Longrightarrow> mod4 (acoord G h - acoord G g) = a A G B"
begin

lemma assumes "h \<in> Halfline" "g \<in> Halfline" "i \<in> Halfline" "endpoint G h" "endpoint G g" "endpoint G i"
 "A \<in> h" "B \<in> g" "C \<in> i" shows "a A G B + a B G C =4 a A G C"
proof -
  from assms have angles:"mod4 (acoord G h - acoord G g) = a A G B" " mod4 (acoord G g - acoord G i) = a B G C" 
  "mod4 (acoord G h - acoord G i) = a A G C" by (rule_tac [!] angle_measure)
  define Aa where "Aa = acoord G h" 
  define Bb where "Bb = acoord G g" 
  define Cc where "Cc = acoord G i" 
  have angles_again:"mod4 (Aa - Bb) = a A G B" "mod4 (Bb - Cc) = a B G C" 
  "mod4 (Aa - Cc) = a A G C" using Aa_def Bb_def Cc_def angles by auto
  have "(Aa - Bb) +  (Bb - Cc) =4 (Aa - Bb) + (Bb - Cc)" by (rule eq4_refl)
  then have "mod4 (Aa - Bb) +  (Bb - Cc) =4 (Aa - Bb) + (Bb - Cc)" using delete_mod4 by simp
  then have "(Bb - Cc) + mod4 (Aa - Bb) =4 (Aa - Bb) + (Bb - Cc)"
    by argo
  then have "mod4 (Aa - Bb) + mod4 (Bb - Cc) =4 (Aa - Bb) + (Bb - Cc)"
    by (subst (asm) delete_mod4[symmetric], subst add.commute)
  also have "... =4 Aa - Cc" by (simp add: eq4_refl)
  also have " ... =4  mod4 (Aa - Cc)" by (rule mod4_bestdef)
  finally have "mod4 (Aa - Bb) + mod4 (Bb - Cc) =4  mod4 (Aa - Cc)" by simp
  then show ?thesis using angles_again by simp
qed


lemma assumes "h \<in> Halfline" "g \<in> Halfline" "endpoint G h" "endpoint G g"
 "A \<in> h" "A \<noteq> G" "B \<in> g" "B \<noteq> G"  "between A P B" "P \<notin> h" "P \<notin> g"
shows "\<exists>i \<in> Halfline. endpoint G i \<and> P \<in> i \<and> a A G B + a B G P =4 a A G P"
(* \<exists>i \<in> Halfline. endpoint G i \<and> P \<in> i   is all we need to prove*)

(*if l, m, n are any three half-lines through 0, then
a lOm + a mOn =4 a lOn. *) have " 
end
end