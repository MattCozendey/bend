# the bytes in order: a merge sort of Base, with a closed template argument
import Base

def main(i: List<&2, U32>) -> List<&2, U32>:
  List.sort(~U32, ~U32.is_le, i)
