module

public import Quartic.FiniteEndpointInverseMemo29
import Quartic.FiniteEndpointRows29.Chunk027
public import Quartic.FiniteEndpointMetadata29Data

@[expose] public section

/-! Kernel-checked rows of the actual quartic multiplication matrix. -/
namespace Quartic.FiniteEndpointRows29
open FiniteEndpointChecker
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 64000000

certify_sparse_rows certificate from "certificates/finite/n29/sparse.bin" inverse_file "certificates/finite/n29/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse29.binaryInverse row_fn Quartic.FiniteEndpointMetadata29Data.naturalRow nwords 562 start_index 35840 row_count 64

theorem chunk_560 (i : Fin 64) (hi : 35840+i.val < 35960) :
    xorSum ((FiniteEndpointMetadata29Data.naturalRow (35840+i.val)).map
      FiniteEndpointInverse29.binaryInverse) = 2^(35840+i.val) := by
  fin_cases i
  · exact certificate.row_35840
  · exact certificate.row_35841
  · exact certificate.row_35842
  · exact certificate.row_35843
  · exact certificate.row_35844
  · exact certificate.row_35845
  · exact certificate.row_35846
  · exact certificate.row_35847
  · exact certificate.row_35848
  · exact certificate.row_35849
  · exact certificate.row_35850
  · exact certificate.row_35851
  · exact certificate.row_35852
  · exact certificate.row_35853
  · exact certificate.row_35854
  · exact certificate.row_35855
  · exact certificate.row_35856
  · exact certificate.row_35857
  · exact certificate.row_35858
  · exact certificate.row_35859
  · exact certificate.row_35860
  · exact certificate.row_35861
  · exact certificate.row_35862
  · exact certificate.row_35863
  · exact certificate.row_35864
  · exact certificate.row_35865
  · exact certificate.row_35866
  · exact certificate.row_35867
  · exact certificate.row_35868
  · exact certificate.row_35869
  · exact certificate.row_35870
  · exact certificate.row_35871
  · exact certificate.row_35872
  · exact certificate.row_35873
  · exact certificate.row_35874
  · exact certificate.row_35875
  · exact certificate.row_35876
  · exact certificate.row_35877
  · exact certificate.row_35878
  · exact certificate.row_35879
  · exact certificate.row_35880
  · exact certificate.row_35881
  · exact certificate.row_35882
  · exact certificate.row_35883
  · exact certificate.row_35884
  · exact certificate.row_35885
  · exact certificate.row_35886
  · exact certificate.row_35887
  · exact certificate.row_35888
  · exact certificate.row_35889
  · exact certificate.row_35890
  · exact certificate.row_35891
  · exact certificate.row_35892
  · exact certificate.row_35893
  · exact certificate.row_35894
  · exact certificate.row_35895
  · exact certificate.row_35896
  · exact certificate.row_35897
  · exact certificate.row_35898
  · exact certificate.row_35899
  · exact certificate.row_35900
  · exact certificate.row_35901
  · exact certificate.row_35902
  · exact certificate.row_35903

certify_sparse_rows certificate from "certificates/finite/n29/sparse.bin" inverse_file "certificates/finite/n29/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse29.binaryInverse row_fn Quartic.FiniteEndpointMetadata29Data.naturalRow nwords 562 start_index 35904 row_count 56

theorem chunk_561 (i : Fin 64) (hi : 35904+i.val < 35960) :
    xorSum ((FiniteEndpointMetadata29Data.naturalRow (35904+i.val)).map
      FiniteEndpointInverse29.binaryInverse) = 2^(35904+i.val) := by
  fin_cases i
  · exact certificate.row_35904
  · exact certificate.row_35905
  · exact certificate.row_35906
  · exact certificate.row_35907
  · exact certificate.row_35908
  · exact certificate.row_35909
  · exact certificate.row_35910
  · exact certificate.row_35911
  · exact certificate.row_35912
  · exact certificate.row_35913
  · exact certificate.row_35914
  · exact certificate.row_35915
  · exact certificate.row_35916
  · exact certificate.row_35917
  · exact certificate.row_35918
  · exact certificate.row_35919
  · exact certificate.row_35920
  · exact certificate.row_35921
  · exact certificate.row_35922
  · exact certificate.row_35923
  · exact certificate.row_35924
  · exact certificate.row_35925
  · exact certificate.row_35926
  · exact certificate.row_35927
  · exact certificate.row_35928
  · exact certificate.row_35929
  · exact certificate.row_35930
  · exact certificate.row_35931
  · exact certificate.row_35932
  · exact certificate.row_35933
  · exact certificate.row_35934
  · exact certificate.row_35935
  · exact certificate.row_35936
  · exact certificate.row_35937
  · exact certificate.row_35938
  · exact certificate.row_35939
  · exact certificate.row_35940
  · exact certificate.row_35941
  · exact certificate.row_35942
  · exact certificate.row_35943
  · exact certificate.row_35944
  · exact certificate.row_35945
  · exact certificate.row_35946
  · exact certificate.row_35947
  · exact certificate.row_35948
  · exact certificate.row_35949
  · exact certificate.row_35950
  · exact certificate.row_35951
  · exact certificate.row_35952
  · exact certificate.row_35953
  · exact certificate.row_35954
  · exact certificate.row_35955
  · exact certificate.row_35956
  · exact certificate.row_35957
  · exact certificate.row_35958
  · exact certificate.row_35959
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

end Quartic.FiniteEndpointRows29
