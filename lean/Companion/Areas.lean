import Companion.AreaChunk00
import Companion.AreaChunk01
import Companion.AreaChunk02
import Companion.AreaChunk03
import Companion.AreaChunk04
import Companion.AreaChunk05
import Companion.AreaChunk06
import Companion.AreaChunk07
import Companion.AreaChunk08
import Companion.AreaChunk09
import Companion.AreaChunk10
import Companion.AreaChunk11
import Companion.AreaChunk12
import Companion.Construction
namespace Companion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def presentationTargets : List Word := [target000, target001, target002, target003, target004, target005, target006, target007, target008, target009, target010, target011, target012, target013, target014, target015, target016, target017, target018, target019, target020, target021, target022, target023, target024, target025, target026, target027, target028, target029, target030, target031, target032, target033, target034, target035, target036, target037, target038, target039, target040, target041, target042, target043, target044, target045, target046, target047, target048, target049, target050, target051, target052, target053, target054, target055, target056, target057, target058, target059, target060, target061, target062, target063, target064, target065, target066, target067, target068, target069, target070, target071, target072, target073, target074, target075, target076, target077, target078, target079, target080, target081, target082, target083, target084, target085, target086, target087, target088, target089, target090, target091, target092, target093, target094, target095, target096, target097, target098, target099, target100, target101, target102, target103, target104, target105, target106, target107, target108, target109, target110, target111, target112, target113, target114, target115, target116, target117, target118, target119]
theorem presentation_area : ∀ t ∈ presentationTargets, HasArea suppliedGame t 42 := by
  intro t h
  simp only [presentationTargets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact area000
  · exact area001
  · exact area002
  · exact area003
  · exact area004
  · exact area005
  · exact area006
  · exact area007
  · exact area008
  · exact area009
  · exact area010
  · exact area011
  · exact area012
  · exact area013
  · exact area014
  · exact area015
  · exact area016
  · exact area017
  · exact area018
  · exact area019
  · exact area020
  · exact area021
  · exact area022
  · exact area023
  · exact area024
  · exact area025
  · exact area026
  · exact area027
  · exact area028
  · exact area029
  · exact area030
  · exact area031
  · exact area032
  · exact area033
  · exact area034
  · exact area035
  · exact area036
  · exact area037
  · exact area038
  · exact area039
  · exact area040
  · exact area041
  · exact area042
  · exact area043
  · exact area044
  · exact area045
  · exact area046
  · exact area047
  · exact area048
  · exact area049
  · exact area050
  · exact area051
  · exact area052
  · exact area053
  · exact area054
  · exact area055
  · exact area056
  · exact area057
  · exact area058
  · exact area059
  · exact area060
  · exact area061
  · exact area062
  · exact area063
  · exact area064
  · exact area065
  · exact area066
  · exact area067
  · exact area068
  · exact area069
  · exact area070
  · exact area071
  · exact area072
  · exact area073
  · exact area074
  · exact area075
  · exact area076
  · exact area077
  · exact area078
  · exact area079
  · exact area080
  · exact area081
  · exact area082
  · exact area083
  · exact area084
  · exact area085
  · exact area086
  · exact area087
  · exact area088
  · exact area089
  · exact area090
  · exact area091
  · exact area092
  · exact area093
  · exact area094
  · exact area095
  · exact area096
  · exact area097
  · exact area098
  · exact area099
  · exact area100
  · exact area101
  · exact area102
  · exact area103
  · exact area104
  · exact area105
  · exact area106
  · exact area107
  · exact area108
  · exact area109
  · exact area110
  · exact area111
  · exact area112
  · exact area113
  · exact area114
  · exact area115
  · exact area116
  · exact area117
  · exact area118
  · exact area119
theorem commutator_area : HasArea suppliedGame target120 42 := area120
theorem presentationTargets_match : presentationTargets = substitutedRelators inputPresentation := by decide +kernel
theorem gadget_relators_area : ∀ t ∈ substitutedRelators inputPresentation, HasArea suppliedGame t 42 := by
  intro t ht
  apply presentation_area
  rwa [presentationTargets_match]
theorem target120_match : target120 = distinguishedCommutator inputPresentation := by decide +kernel
theorem gadget_commutator_area : HasArea suppliedGame (distinguishedCommutator inputPresentation) 42 := by
  rw [← target120_match]
  exact area120
end Companion
