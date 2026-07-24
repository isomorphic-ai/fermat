import Fermat.SixtySeven.ArithmeticCertificate
import Fermat.Irregular.VandiverData

/-!
# Complete low Bernoulli scan at exponent 157

The recurrence table already checked for exponent `67` reaches `B₆₄`.
This file continues the same exact rational recurrence through `B₁₅₄` and
uses it to identify every Bernoulli numerator divisible by `157` in the
classical irregular range.  The result is the two-channel set `{62, 110}`
reported by the exponent-157 proof package.
-/

namespace Fermat.OneHundredFiftySeven.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

@[simp] private theorem bernoulli'_sixtySix :
    bernoulli' 66 =
      (1472600022126335654051619428551932342241899101 : ℚ) / 64722 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_sixtyEight :
    bernoulli' 68 =
      -(78773130858718728141909149208474606244347001 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_70 :
    bernoulli' 70 = (1505381347333367003803076567377857208511438160235 : ℚ) / 4686 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_72 :
    bernoulli' 72 = -(5827954961669944110438277244641067365282488301844260429 : ℚ) / 140100870 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_74 :
    bernoulli' 74 = (34152417289221168014330073731472635186688307783087 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_76 :
    bernoulli' 76 = -(24655088825935372707687196040585199904365267828865801 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_78 :
    bernoulli' 78 = (414846365575400828295179035549542073492199375372400483487 : ℚ) / 3318 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_80 :
    bernoulli' 80 = -(4603784299479457646935574969019046849794257872751288919656867 : ℚ) / 230010 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_82 :
    bernoulli' 82 = (1677014149185145836823154509786269900207736027570253414881613 : ℚ) / 498 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_84 :
    bernoulli' 84 = -(2024576195935290360231131160111731009989917391198090877281083932477 : ℚ) / 3404310 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_86 :
    bernoulli' 86 = (660714619417678653573847847426261496277830686653388931761996983 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_88 :
    bernoulli' 88 = -(1311426488674017507995511424019311843345750275572028644296919890574047 : ℚ) / 61410 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_90 :
    bernoulli' 90 = (1179057279021082799884123351249215083775254949669647116231545215727922535 : ℚ) / 272118 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_92 :
    bernoulli' 92 = -(1295585948207537527989427828538576749659341483719435143023316326829946247 : ℚ) / 1410 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_94 :
    bernoulli' 94 = (1220813806579744469607301679413201203958508415202696621436215105284649447 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_96 :
    bernoulli' 96 = -(211600449597266513097597728109824233673043954389060234150638733420050668349987259 : ℚ) / 4501770 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_98 :
    bernoulli' 98 = (67908260672905495624051117546403605607342195728504487509073961249992947058239 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_100 :
    bernoulli' 100 = -(94598037819122125295227433069493721872702841533066936133385696204311395415197247711 : ℚ) / 33330 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_102 :
    bernoulli' 102 = (3204019410860907078243020782116241775491817197152717450679002501086861530836678158791 : ℚ) / 4326 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_104 :
    bernoulli' 104 = -(319533631363830011287103352796174274671189606078272738327103470162849568365549721224053 : ℚ) / 1590 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_106 :
    bernoulli' 106 = (36373903172617414408151820151593427169231298640581690038930816378281879873386202346572901 : ℚ) / 642 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_108 :
    bernoulli' 108 = -(3469342247847828789552088659323852541399766785760491146870005891371501266319724897592306597338057 : ℚ) / 209191710 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_110 :
    bernoulli' 110 = (7645992940484742892248134246724347500528752413412307906683593870759797606269585779977930217515 : ℚ) / 1518 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_112 :
    bernoulli' 112 = -(2650879602155099713352597214685162014443151499192509896451788427680966756514875515366781203552600109 : ℚ) / 1671270 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_114 :
    bernoulli' 114 = (21737832319369163333310761086652991475721156679090831360806110114933605484234593650904188618562649 : ℚ) / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_116 :
    bernoulli' 116 = -(309553916571842976912513458033841416869004128064329844245504045721008957524571968271388199595754752259 : ℚ) / 1770 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_118 :
    bernoulli' 118 = (366963119969713111534947151585585006684606361080699204301059440676414485045806461889371776354517095799 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_120 :
    bernoulli' 120 = -(51507486535079109061843996857849983274095170353262675213092869167199297474922985358811329367077682677803282070131 : ℚ) / 2328255930 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_122 :
    bernoulli' 122 = (49633666079262581912532637475990757438722790311060139770309311793150683214100431329033113678098037968564431 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_124 :
    bernoulli' 124 = -(95876775334247128750774903107542444620578830013297336819553512729358593354435944413631943610268472689094609001 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_126 :
    bernoulli' 126 = (5556330281949274850616324408918951380525567307126747246796782304333594286400508981287241419934529638692081513802696639 : ℚ) / 4357878 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_128 :
    bernoulli' 128 = -(267754707742548082886954405585282394779291459592551740629978686063357792734863530145362663093519862048495908453718017 : ℚ) / 510 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_130 :
    bernoulli' 130 = (1928215175136130915645299522271596435307611010164728458783733020528548622403504078595174411693893882739334735142562418015 : ℚ) / 8646 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_132 :
    bernoulli' 132 = -(410951945846993378209020486523571938123258077870477502433469747962650070754704863812646392801863686694106805747335370312946831 : ℚ) / 4206930 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_134 :
    bernoulli' 134 = (264590171870717725633635737248879015151254525593168688411918554840667765591690540727987316391252434348664694639349484190167 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_136 :
    bernoulli' 136 = -(84290226343367405131287578060366193649336612397547435767189206912230442242628212786558235455817749737691517685781164837036649737 : ℚ) / 4110 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_138 :
    bernoulli' 138 = (2694866548990880936043851683724113040849078494664282483862150893060478501559546243423633375693325757795709438325907154973590288136429 : ℚ) / 274386 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_140 :
    bernoulli' 140 = -(3289490986435898803930699548851884006880537476931130981307467085162504802973618096693859598125274741604181467826651144393874696601946049 : ℚ) / 679470 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_142 :
    bernoulli' 142 = (14731853280888589565870080442453214239804217023990642676194878997407546061581643106569966189211748270209483494554402556608073385149191 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_144 :
    bernoulli' 144 = -(3050244698373607565035155836901726357405007104256566761884191852434851033744761276392695669329626855965183503295793517411526056244431024612640493 : ℚ) / 2381714790 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_146 :
    bernoulli' 146 = (4120570026280114871526113315907864026165545608808541153973817680034790262683524284855810008621905238290240143481403022987037271683989824863 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_148 :
    bernoulli' 148 = -(1691737145614018979865561095112166189607682852147301400816480675916957871178648433284821493606361235973346584667336181793937950344828557898347149 : ℚ) / 4470 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_150 :
    bernoulli' 150 = (463365579389162741443284425811806264982233725425295799852299807325379315501572305760030594769688296308375193913787703707693010224101613904227979066275 : ℚ) / 2162622 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_152 :
    bernoulli' 152 = -(3737018141155108502105892888491282165837489531488932951768507127182409731328472084456653639812530140212355374618917309552824925858430886313795805601 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

@[simp] private theorem bernoulli'_154 :
    bernoulli' 154 = (10259718682038021051027794238379184461025738652460569233992776489750881337506863808448685054322627708245455888249006715516690124228801409697850408284121 : ℚ) / 138 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd, Nat.choose]

/-! ## Public scan and exceptional values -/

/-- Reuse the common definition of an irregular-index scan. -/
abbrev irregularIndices :=
  Fermat.SixtySeven.ArithmeticCertificate.irregularIndices

/-- The first exceptional Bernoulli number, as printed in the source
package. -/
theorem bernoulli_62_exact :
    bernoulli 62 =
      (12300585434086858541953039857403386151 : ℚ) / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  norm_num

/-- The second exceptional Bernoulli number, as printed in the source
package. -/
theorem bernoulli_110_exact :
    bernoulli 110 =
      (7645992940484742892248134246724347500528752413412307906683593870759797606269585779977930217515 : ℚ) /
        1518 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli'_110

/-- The complete low Bernoulli scan: the only even indices in `[2,154]`
whose reduced Bernoulli numerator has a factor `157` are `62` and `110`. -/
theorem irregularIndices_oneHundredFiftySeven :
    irregularIndices 157 = {62, 110} := by
  ext n
  simp only [irregularIndices,
    Fermat.SixtySeven.ArithmeticCertificate.irregularIndices,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn2, hn154⟩, heven, hdvd⟩
    interval_cases n <;>
      norm_num [bernoulli_eq_bernoulli'_of_ne_one,
        bernoulli'_eq_zero_of_odd] at heven
    all_goals
      norm_num [bernoulli_eq_bernoulli'_of_ne_one,
        bernoulli'_eq_zero_of_odd] at hdvd
    all_goals norm_num
  · rintro (rfl | rfl) <;>
      norm_num [bernoulli_eq_bernoulli'_of_ne_one]

/-- Implication-form API consumed by the finite-channel second-case proof. -/
theorem completeIrregularScan
    (j : ℕ) (hj : j ∈ Fermat.Irregular.VandiverData.indices 157)
    (hirregular : (157 : ℤ) ∣ (bernoulli j).num) :
    j = 62 ∨ j = 110 := by
  have hj' : 2 ≤ j ∧ j ≤ 154 ∧ Even j := by
    simpa [Fermat.Irregular.VandiverData.indices, and_assoc] using hj
  have hmem : j ∈ irregularIndices 157 := by
    simp only [irregularIndices,
      Fermat.SixtySeven.ArithmeticCertificate.irregularIndices,
      Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hj'.1, hj'.2.1⟩, hj'.2.2, hirregular⟩
  rw [irregularIndices_oneHundredFiftySeven] at hmem
  simpa using hmem

/-- The numerator of `B₆₂` contains exactly one factor `157`. -/
theorem bernoulli_62_numerator_factorization :
    (12300585434086858541953039857403386151 : ℕ) =
      157 * 78347677924120118101611718836964243 := by
  norm_num

theorem bernoulli_62_numerator_not_dvd_sq :
    ¬157 ^ 2 ∣ (12300585434086858541953039857403386151 : ℕ) := by
  norm_num

/-- The numerator of `B₁₁₀` also contains exactly one factor `157`. -/
theorem bernoulli_110_numerator_factorization :
    (7645992940484742892248134246724347500528752413412307906683593870759797606269585779977930217515 : ℕ) =
      157 *
        48700591977609827339160090743467181532030270149122980297347731660890430613182075031706561895 := by
  norm_num

theorem bernoulli_110_numerator_not_dvd_sq :
    ¬157 ^ 2 ∣
      (7645992940484742892248134246724347500528752413412307906683593870759797606269585779977930217515 : ℕ) := by
  norm_num

end Fermat.OneHundredFiftySeven.IrregularScan
