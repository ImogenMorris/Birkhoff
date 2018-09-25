theory Metric_Geometry3 imports Main Real

begin
(*to do: change to bij_betw, separate locales, define line set, make simpler*)

(*
typedecl pt
consts line:: "pt set"
consts distance:: "[pt, pt] \<Rightarrow> real"
consts angle:: "pt => pt \<Rightarrow> pt \<Rightarrow> real "*)

(*class Line_Measure =
  fixes isLine :: "'a set \<Rightarrow> bool"
  fixes d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  fixes coord :: "'a set \<Rightarrow> 'a \<Rightarrow> real"
  assumes line_symmetry: "d A B  = d B A "
  and line_nonneg: "d A B \<ge> 0"*)
 (* fixes coord :: "'p set \<Rightarrow> 'p \<Rightarrow> real"*)
 (* and line_measure1: "isLine l \<Longrightarrow> bij (coord l)"
  and line_measure2: "\<lbrakk>isLine l; A \<in> l; B \<in> l\<rbrakk> \<Longrightarrow> \<bar>coord l A - coord l B\<bar> = d A B"
  and line_measure3: "isLine l \<Longrightarrow> range (coord l) = (UNIV::real set)" (*Do we need isLine l assumption?
perhaps we don't even care what coord is defined to be in these cases.*)
(*The range of coord l would even need to depend on l! Is this possible/allowed? We might get a contradiction.*)
  and line_measure4: "isLine l \<Longrightarrow> {coord l x|x. x \<in> l} = (UNIV::real set)"*)
 (* "\<And> l. isLine l \<Longrightarrow> \<exists> (f:: ('p \<Rightarrow> real)) . (bij f \<and> (\<bar>f A - f B\<bar> = d A B) 
\<and> ((range f) = R) \<and> ({f x|x. x \<in> l} = R))"*) 

definition "correspondence C (A::'a set) (B::'b set) \<equiv> (C={c.\<exists>(a::'a) (b::'b).c=(a,b)})\<and>
((\<forall>a\<in>A.\<exists>!c\<in>C.\<exists>b\<in>B.(c=(a,b)))\<and>(\<forall>b\<in>B.\<exists>!c\<in>C.\<exists>a\<in>A.(c=(a,b))))"

definition "correspondence C A B \<Longrightarrow> ex1 C a \<equiv> THE b. (a,b) \<in> C"

definition "correspondence C A B \<Longrightarrow> ex2 C b \<equiv> THE a. (a,b) \<in> C"

definition "invCorrespondence C' C \<equiv> \<exists> A B. correspondence C A B \<and> correspondence C' B A"
(*show uniqueness and existence*)

locale Line_Measure =
  fixes isLine :: "'p set \<Rightarrow> bool"
  fixes Coord  :: "'p set \<Rightarrow> ('p \<times> real) set set"
  assumes
 (* and line_measure1: "isLine l \<Longrightarrow> correspondence (Coord l) l (UNIV:: real set)"
  and line_measure2:  "\<lbrakk>(l1,r1) \<in> Coord l; (l2,r2) \<in> Coord l\<rbrakk> \<Longrightarrow> \<bar>r1 - r2\<bar> = d l1 l2"*)
  brossard_line_measure1: "isLine l \<Longrightarrow> \<exists> x. x \<in> Coord l"
  and brossard_line_measure2: "\<lbrakk>isLine l; x \<in> Coord l\<rbrakk> \<Longrightarrow> correspondence x l (UNIV::real set)"
  and brossard_line_measure3: "\<lbrakk>x_i \<in> Coord l ; isLine l ; correspondence x_j l (UNIV::real set)\<rbrakk> 
 \<Longrightarrow> ((x_j \<in> Coord l) \<equiv>  \<forall> A \<in> l. \<forall> B \<in> l. \<bar>ex1 x_i A - ex1 x_i B\<bar> = \<bar>ex1 x_j A - ex1 x_j B\<bar> )"
(* if this corresponds to Brossard we don't need to postulate d!*)
(*and brossard_line_measure "isLine l \<Longrightarrow> \<exists> X. X = {x. correspondence x l R} \<and> \<exists> xi \<in> X xj. correspondence xj l R
\<longrightarrow> (xj \<in> X \<longleftrightarrow> \<forall> A \<in> l B \<in> l. \<exists> riA riB rjA rjB. (*want to write it more user-friendlyly*)*)
  and point_line_brossard_line2: "A \<noteq> B \<Longrightarrow> \<exists>! l. isLine l \<and> A \<in> l \<and> B \<in> l" 
  and brossard_line1: "\<exists> (A::'p) B. A \<noteq> B"
  and brossard_line3: "\<exists> A B C. \<not>(\<exists> l. isLine l \<and> A \<in> l \<and> B \<in> l \<and> C \<in> l)" 
(*Perhaps can prove brossard_line1 from this ? ? ? Plus some of the other axioms... not obvious though.*)
context Line_Measure
begin
(*also want to prove that d is a metric*)

lemma second_point: "\<exists> B. (A::'p) \<noteq> B"
  by (metis brossard_line1)

lemma line_through_point: "\<exists> l. isLine l \<and> (A::'p) \<in> l"
  by (metis second_point point_line_brossard_line2)


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

lemma line_bestdef:    shows "isLine (line A B)"
                         and "A \<in> (line A B)" and "B \<in> (line A B)"
  proof (case_tac [!] "A=B")
    assume "A\<noteq>B"
    then show "isLine (line A B)" and "A \<in> (line A B)" and "B \<in> (line A B)" by (rule_tac [!] unique_line)
    next
    assume "A=B"
    then have new_line_def:  "line A B = (SOME l. isLine l \<and> A \<in> l)" by (simp add: line_def)
    obtain C where "C\<noteq>A" using second_point by fastforce
    then have "isLine (line A C) \<and> A \<in> (line A C)" by (simp add: unique_line)
    then have "\<exists> l. isLine l \<and> A \<in> l" by auto
    then have "isLine (line A B) \<and> A \<in> (line A B)" by (subst new_line_def, subst new_line_def, rule someI_ex)
    then show "isLine (line A B)"  and "A \<in> (line A B)" by auto
    then show "B \<in> (line A B)" using `A = B` by auto
  qed

definition "x \<in> Coord (line A B) \<Longrightarrow> distance_rel x A B == \<bar>ex1 x A - ex1 x B\<bar>"
(*then we prove it's same for all x and redefine it*)

(*for betweenness we can assume A \<noteq> B*)
definition "\<lbrakk>C \<in> (line A B); x \<in> Coord (line A B)\<rbrakk> \<Longrightarrow> 
between_rel x A B C == (ex1 x A < ex1 x B \<and> ex1 x B < ex1 x C \<or> ex1 x C < ex1 x B \<and> ex1 x B < ex1 x A)"

lemma assumes "between_rel x A B C"
        shows "A \<noteq> B" and "B \<noteq> C" and "A \<noteq> C"
oops
(*lemma assumes "between_rel x A B C"
        shows "ex1 x A < ex1 x B \<and> ex1 x B < ex1 x C \<or> ex1 x C < ex1 x B \<and> ex1 x B < ex1 x A"
oops*)

lemma 
"C \<in> (line A B)\<Longrightarrow>\<exists>(between::('p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool)). 
                                       \<forall> x \<in> Coord (line A B). between A B C = between_rel x A B C"
(* it should automatically be unique.*)
proof-
  assume "C \<in> (line A B)"
  have "isLine (line A B)" using line_bestdef by auto
  then obtain x_i where x_i_def:"x_i \<in> Coord (line A B)" using brossard_line_measure1 by auto
  show ?thesis
  proof (rule exI,rule ballI)
    fix x_j
    assume "x_j \<in> Coord (line A B)"
    from `isLine (line A B)` this have "correspondence x_j (line A B) (UNIV::real set)" 
      by (rule brossard_line_measure2)
    from x_i_def `isLine (line A B)` this
    have "(x_j \<in> Coord (line A B)) \<equiv> (\<forall>X\<in>(line A B). \<forall>Y\<in>(line A B). \<bar>ex1 x_i X - ex1 x_i Y\<bar> = \<bar>ex1 x_j X - ex1 x_j Y\<bar>)"
      by (rule brossard_line_measure3)
    from this `x_j \<in> Coord (line A B)`
    have rel_distance:"\<forall>X\<in>(line A B). \<forall>Y\<in>(line A B). \<bar>ex1 x_i X - ex1 x_i Y\<bar> = \<bar>ex1 x_j X - ex1 x_j Y\<bar>"
      by simp
    have "A \<in> (line A B)" and "B \<in> (line A B)" by (rule line_bestdef,rule line_bestdef)
    from rel_distance this have 
      1:"(ex1 x_i A - ex1 x_i B = ex1 x_j A - ex1 x_j B)\<or>(ex1 x_i A - ex1 x_i B = ex1 x_j B - ex1 x_j A)"
      by fastforce
    from rel_distance `A \<in> (line A B)` `C \<in> (line A B)` have 
      2:"(ex1 x_i A - ex1 x_i C = ex1 x_j A - ex1 x_j C)\<or>(ex1 x_i A - ex1 x_i C = ex1 x_j C - ex1 x_j A)"
      by fastforce 
    from rel_distance `B \<in> (line A B)` `C \<in> (line A B)` have 
      3:"(ex1 x_i B - ex1 x_i C = ex1 x_j B - ex1 x_j C)\<or>(ex1 x_i B - ex1 x_i C = ex1 x_j C - ex1 x_j B)"
      by fastforce 
    show "between_rel x_i A B C = between_rel x_j A B C"
    proof (cases "between_rel x_i A B C")
      case True
      consider (a) "ex1 x_i A < ex1 x_i B \<and> ex1 x_i B < ex1 x_i C" 
             | (b) "ex1 x_i C < ex1 x_i B \<and> ex1 x_i B < ex1 x_i A"
      using `C \<in> (line A B)` x_i_def `between_rel x_i A B C` by (auto simp: between_rel_def)
      then consider (a) "(ex1 x_i A - ex1 x_i B = ex1 x_j A - ex1 x_j B) \<and>
                         (ex1 x_i A - ex1 x_i C = ex1 x_j A - ex1 x_j C) \<and>
                         (ex1 x_i B - ex1 x_i C = ex1 x_j B - ex1 x_j C)" 
                  | (b) "(ex1 x_i A - ex1 x_i B = ex1 x_j B - ex1 x_j A) \<and>
                         (ex1 x_i A - ex1 x_i C = ex1 x_j C - ex1 x_j A) \<and>
                         (ex1 x_i B - ex1 x_i C = ex1 x_j C - ex1 x_j B)"
         proof - (*we will show a disjunction and then show the thesis*)
        
         


(*definition "x \<in> Coord (line A B) \<Longrightarrow> between_rel x A B C == (distance_rel x A C = distance_rel x A B + distance_rel x B C)"
 This differs from Brossard but perhaps equivalent. Brossard proves it.*)

definition 
"between == (THE between. \<forall> l. isLine l \<longrightarrow> (\<forall> A \<in> l.  \<forall> B \<in> l.  \<forall> C \<in> l. \<forall>x \<in> Coord l.  between A B C = between_rel x A B C))"

lemma ""

  
lemma pos_def: "(d A B = 0) \<equiv> (A = B)"
proof -
  have "(d A B = 0) \<Longrightarrow> (A = B)" sorry
  moreover have "(A = B) \<Longrightarrow>(d A B = 0)"
  proof -
    assume "A = B" 
    obtain l where "isLine l \<and> (A::'p) \<in> l" using line_through_point by auto
    then have "correspondence (Coord l) l (UNIV:: real set)" by (simp add: line_measure1)
    
    (*Cannot be proven without postulating existence of a line! Also, by the order of Birkhoff's 
paper, it ought to be proven without the point-line postulate.*)
  qed
  ultimately show "(d A B = 0) \<equiv> (A = B)" 
    by linarith



lemma Lines_have_points: assumes "isLine l"
                           shows "\<exists> A B. A \<in> l \<and> B \<in> l \<and> A \<noteq> B"

  

lemma Unique_intersection: assumes "isLine l" and "isline m" and "l\<noteq>m"
                             shows "\<exists>!X. X \<in> l \<and> X \<in> m"

lemma Lines_are_dense:  assumes "isLine l" 
                          shows  "A \<in>l \<and> B \<in> l \<Longrightarrow> \<exists>C. C \<in> l \<and> C \<noteq>A \<and> C \<noteq> B"

definition "isHalfLine h == (\<forall> X. X \<in> h  \<longleftrightarrow>( \<exists> (l::line) A G. A \<in> l \<and> G \<in> l \<and> \<not> between A X G))"

definition "HalfLine (l::line) A G = {X. X \<in> l \<and> \<not> between A X G}"

lemma Half_Line_Well_Def: "isHalfLine (HalfLine l A G)"
  proof (subst isHalfLine_def, subst HalfLine_def, safe)

lemma HalfLine_is_half_a_line: assumes "isLine l"
shows "\<exists> A G B. A \<in> l \<and> G \<in> l \<and> B \<in> l \<and> between A G B  \<and> l = (HalfLine l A G) \<union> {x. x=G} \<union> (HalfLine l G B)"

    
    
  

end

locale Angle_Measure = Line_Measure + 
  fixes m :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> R"
  assumes "m A B C \<in> R \<Longrightarrow> (A \<noteq> B \<and> B \<noteq> C)"

context Angle_Measure

begin

definition "Am A B C = m A B C mod 4"

definition "m' (l::line) (m::line) = m (SOME A. A \<in> l) (SOME G. G \<in> l \<and> G \<in> m) (SOME B. B \<in> m)" (* how to specify properties of A,G,B?*)
(* Do we need to specify the point of intersection? Birkhoff writes angle lOm*)
lemma Angle_of_halflines_welldef: assumes "A \<noteq> G" and ""


end
  
  
  
 





end