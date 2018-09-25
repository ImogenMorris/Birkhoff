theory Metric_Geometry2 imports Main Real

begin

(*
typedecl pt
consts line:: "pt set"
consts distance:: "[pt, pt] \<Rightarrow> real"
consts angle:: "pt => pt \<Rightarrow> pt \<Rightarrow> real "*)

(*(the \<circ> f) x*)

locale Line_Measure =
  fixes isLine :: "'p set \<Rightarrow> bool"
  fixes d :: "'p \<Rightarrow> 'p \<Rightarrow> real"
  fixes coord :: "'p set \<Rightarrow> 'p \<Rightarrow> real option"
  assumes line_symmetry: "d A B  = d B A "
  and line_nonneg: "d A B \<ge> 0"
  and definedness: "isLine l \<Longrightarrow> (dom (coord l) = l)"
  and line_measure1: "isLine l \<Longrightarrow> bij ((coord l) |` l)"
  and line_measure2: "\<lbrakk>isLine l; A \<in> l; B \<in> l\<rbrakk> \<Longrightarrow> \<bar>(the \<circ> coord l) A - (the \<circ> coord l) B\<bar> = d A B"
  and line_measure3: "isLine l \<Longrightarrow> range ((coord l) |` l) = (UNIV::real option set)" (*Do we need isLine l assumption?
perhaps we don't even care what coord is defined to be in these cases.*)
(*The range of coord l would even need to depend on l! Is this possible/allowed? We might get a contradiction.*)
(*  and line_measure4: "isLine l \<Longrightarrow> {coord l x|x. x \<in> l} = (UNIV::real option set)"*)
 (* "\<And> l. isLine l \<Longrightarrow> \<exists> (f:: ('p \<Rightarrow> real)) . (bij f \<and> (\<bar>f A - f B\<bar> = d A B) 
\<and> ((range f) = R) \<and> ({f x|x. x \<in> l} = R))"*) 


locale Brossard_Line_Measure =
  fixes Coord :: "'p set \<Rightarrow> ('p \<Rightarrow> real option) set"
  fixes isLine :: "'p set \<Rightarrow> bool"
  assumes
  brossard_line_measure1: "isLine l \<Longrightarrow> \<exists> x. x \<in> Coord l"
  and brossard_line_measure2: "isLine l \<Longrightarrow> x \<in> Coord l \<Longrightarrow> bij_betw x l (UNIV::real option set)" 
(*perhaps this is needed in metric geometry too! - does it mean that dom x = l? no but does it matter
- it matters that x is at least defined on l! *)
  and brossard_line_measure3: "isLine l \<Longrightarrow> \<lbrakk>xi \<in> Coord l ; bij_betw xj l (UNIV::real option set)\<rbrakk> 
\<Longrightarrow> ((xj \<in> Coord l) \<equiv> \<forall> A \<in> l. \<forall> B \<in> l. \<bar>(the \<circ> xi) A - (the \<circ> xi) B\<bar> = \<bar>(the \<circ> xj) A - (the \<circ> xj) B\<bar>)"
(*and brossard_line_measure "isLine l \<Longrightarrow> \<exists> X. X = {x. correspondence x l R} \<and> \<exists> xi \<in> X xj. correspondence xj l R
\<longrightarrow> (xj \<in> X \<longleftrightarrow> \<forall> A \<in> l B \<in> l. \<exists> riA riB rjA rjB. (*want to write it more user-friendlyly*)*)
  and point_line_brossard_line2: "A \<noteq> B \<Longrightarrow> \<exists>! l. isLine l \<and> A \<in> l \<and> B \<in> l" 
  and brossard_line1: "\<exists> (A::'p) B. A \<noteq> B"
  and brossard_line3: "\<exists> A B C. \<not>(\<exists> l. isLine l \<and> A \<in> l \<and> B \<in> l \<and> C \<in> l)" 
context Brossard_Line_Measure begin

definition "x \<in> coord l \<Longrightarrow> distance_rel x A B == \<bar>(the \<circ> x) A - (the \<circ> x) B\<bar>"
(*then we prove it's same for all xi and redefine it*)
definition "between_rel x A B C == (distance_rel x A C = distance_rel x A B + distance_rel x B C)"
 (*This differs from Brossard but perhaps equivalent. Seems simpler anyhow.*)
definition "isLine l \<Longrightarrow> \<lbrakk> A \<in> l; B \<in> l; C \<in> l\<rbrakk> \<Longrightarrow> 
brossard_between_rel x A B C == ((the \<circ> x) A < (the \<circ> x) B \<and> (the \<circ> x) B < (the \<circ> x) C \<or> (the \<circ> x) C < (the \<circ> x) B \<and> (the \<circ> x) B < (the \<circ> x) A)"

lemma "\<lbrakk> A \<in> l; B \<in> l; C \<in> l; x \<in> Coord l\<rbrakk> \<Longrightarrow> \<exists>! between. between A B C = between_rel x A B C"
sorry

declare[[show_types]]
(*A B C depend on l, and somehow this means between does too, but how to tell Isabelle that?*)
definition 
"between == (THE between. \<forall> l. isLine l \<longrightarrow> (\<forall> A \<in> l.  \<forall> B \<in> l.  \<forall> C \<in> l. \<forall>x \<in> Coord l.  between A B C = between_rel x A B C))"

lemma ""

end
end