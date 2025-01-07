import TrainingData.InfoTree.ToJson
import TrainingData.Utils.HammerBlacklist

open Lean

/-- Whenever `hammerRecommendationBlackList` is updated, `HammerBlacklist.jsonl` can be updated by
    running `(lake exe update_hammer_blacklist) > TrainingData/Utils/HammerBlacklist.jsonl` -/
def main : IO UInt32 := do
  let sortedHammerRecommendationBlackList := sortedHammerRecommendationBlackList.map Json.str
  let data := Json.mkObj [
      ("hammerBlacklist", Json.arr sortedHammerRecommendationBlackList)
    ]
  IO.println s!"{data.compress}"
  return 0
