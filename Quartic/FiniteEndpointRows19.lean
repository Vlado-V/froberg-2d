import Quartic.FiniteEndpointRows19.Chunk000
import Quartic.FiniteEndpointRows19.Chunk001
import Quartic.FiniteEndpointRows19.Chunk002
import Quartic.FiniteEndpointRows19.Chunk003
import Quartic.FiniteEndpointRows19.Chunk004
import Quartic.FiniteEndpointRows19.Chunk005
import Quartic.FiniteEndpointRows19.Chunk006
import Quartic.FiniteEndpointRows19.Chunk007
import Quartic.FiniteEndpointChunks

namespace Quartic.FiniteEndpointRows19
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

theorem all_rows_checked : ∀i : Nat, i < 7315 →
    xorSum ((FiniteEndpointMetadata19Data.naturalRow i).map FiniteEndpointInverse19.binaryInverse) = 2^i := by
  refine FiniteEndpointChunks.forall_lt_of_fin_chunks
    (fun i => xorSum ((FiniteEndpointMetadata19Data.naturalRow i).map FiniteEndpointInverse19.binaryInverse)=2^i) 7315 64 (by decide) ?_
  intro k j h
  change Fin 115 at k
  fin_cases k
  · exact chunk_0 j h
  · exact chunk_1 j h
  · exact chunk_2 j h
  · exact chunk_3 j h
  · exact chunk_4 j h
  · exact chunk_5 j h
  · exact chunk_6 j h
  · exact chunk_7 j h
  · exact chunk_8 j h
  · exact chunk_9 j h
  · exact chunk_10 j h
  · exact chunk_11 j h
  · exact chunk_12 j h
  · exact chunk_13 j h
  · exact chunk_14 j h
  · exact chunk_15 j h
  · exact chunk_16 j h
  · exact chunk_17 j h
  · exact chunk_18 j h
  · exact chunk_19 j h
  · exact chunk_20 j h
  · exact chunk_21 j h
  · exact chunk_22 j h
  · exact chunk_23 j h
  · exact chunk_24 j h
  · exact chunk_25 j h
  · exact chunk_26 j h
  · exact chunk_27 j h
  · exact chunk_28 j h
  · exact chunk_29 j h
  · exact chunk_30 j h
  · exact chunk_31 j h
  · exact chunk_32 j h
  · exact chunk_33 j h
  · exact chunk_34 j h
  · exact chunk_35 j h
  · exact chunk_36 j h
  · exact chunk_37 j h
  · exact chunk_38 j h
  · exact chunk_39 j h
  · exact chunk_40 j h
  · exact chunk_41 j h
  · exact chunk_42 j h
  · exact chunk_43 j h
  · exact chunk_44 j h
  · exact chunk_45 j h
  · exact chunk_46 j h
  · exact chunk_47 j h
  · exact chunk_48 j h
  · exact chunk_49 j h
  · exact chunk_50 j h
  · exact chunk_51 j h
  · exact chunk_52 j h
  · exact chunk_53 j h
  · exact chunk_54 j h
  · exact chunk_55 j h
  · exact chunk_56 j h
  · exact chunk_57 j h
  · exact chunk_58 j h
  · exact chunk_59 j h
  · exact chunk_60 j h
  · exact chunk_61 j h
  · exact chunk_62 j h
  · exact chunk_63 j h
  · exact chunk_64 j h
  · exact chunk_65 j h
  · exact chunk_66 j h
  · exact chunk_67 j h
  · exact chunk_68 j h
  · exact chunk_69 j h
  · exact chunk_70 j h
  · exact chunk_71 j h
  · exact chunk_72 j h
  · exact chunk_73 j h
  · exact chunk_74 j h
  · exact chunk_75 j h
  · exact chunk_76 j h
  · exact chunk_77 j h
  · exact chunk_78 j h
  · exact chunk_79 j h
  · exact chunk_80 j h
  · exact chunk_81 j h
  · exact chunk_82 j h
  · exact chunk_83 j h
  · exact chunk_84 j h
  · exact chunk_85 j h
  · exact chunk_86 j h
  · exact chunk_87 j h
  · exact chunk_88 j h
  · exact chunk_89 j h
  · exact chunk_90 j h
  · exact chunk_91 j h
  · exact chunk_92 j h
  · exact chunk_93 j h
  · exact chunk_94 j h
  · exact chunk_95 j h
  · exact chunk_96 j h
  · exact chunk_97 j h
  · exact chunk_98 j h
  · exact chunk_99 j h
  · exact chunk_100 j h
  · exact chunk_101 j h
  · exact chunk_102 j h
  · exact chunk_103 j h
  · exact chunk_104 j h
  · exact chunk_105 j h
  · exact chunk_106 j h
  · exact chunk_107 j h
  · exact chunk_108 j h
  · exact chunk_109 j h
  · exact chunk_110 j h
  · exact chunk_111 j h
  · exact chunk_112 j h
  · exact chunk_113 j h
  · exact chunk_114 j h

end Quartic.FiniteEndpointRows19
