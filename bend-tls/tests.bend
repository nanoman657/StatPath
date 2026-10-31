# tests.bend: SHA-256 cases. Expected digests come from hashlib (see
# gen_tests.py). Run: bend tests.bend   (and -o tests for native)

import Base
import ./sha256.bend as S

type Case is Data:
  Case{name: String, got: String, want: String}

def case_(name: String, +input: String, want: String) -> Case:
  Case{name, S.sha256_hex(S.bytes_of(input)), want}

def case_raw(name: String, +input: List<&2, U32>, want: String) -> Case:
  Case{name, S.sha256_hex(input), want}

def cases() -> List<&2, Case>:
  case_("empty", "", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855") <>
  case_("abc", "abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") <>
  case_("nist-56", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1") <>
  case_("len-1", "a", "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb") <>
  case_("len-3", "aho", "2fe3269fa210706de21ff97cc964590ec5bddd6677885fc55cfa6bfd94924822") <>
  case_("len-55", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29g", "5edecfc69da5128efb99ad852935e4e8577d6014b72e0c9023ffd511aa45dc01") <>
  case_("len-56", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gn", "aa9b31d71cf6d3faf359446857a56ad83435117e212bbe4b987dfd925208e53e") <>
  case_("len-57", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnu", "e28aa4e33811de661a5fc4a7cfde4f7a50773dc9778173e6e9b1f80f0bdfe165") <>
  case_("len-63", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3a", "63c0d8f0e1d29673920fe4ee348f46689afd80dc5a273b12cfc5d2266948066e") <>
  case_("len-64", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ah", "30cb52d8cd9b53c89d1f421c2fed119b6c11ec7b2f22adac264793982de82828") <>
  case_("len-65", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3aho", "cda221ed8c57bea6ef8f9868984213c5fa9d93f662cf2b7df06ab83c875ed29f") <>
  case_("len-119", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnu", "d55fde8f4c7e7c5ebfe5195c50a532b5cd1811d7655edc6519c4945541ff98f4") <>
  case_("len-120", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuB", "27ded50c38746bf1dc3ff9cdd88b020f47c6b0f2d66388e3a9eca7de9956d0f9") <>
  case_("len-128", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahov", "b5b084399519ddacb8ba8bb0450f99e73192b615519ab280f674b0cd5903b363") <>
  case_("len-1000", "ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX4bipwDKRY5cjqxELSZ6dkryFMT07elszGNU18fmtAHOV29gnuBIPW3ahovCJQX", "f5fd45ac91bf34a41f2c8d47a31030526a8187721abd18ecf6b310c8b6f649c6") <>
  case_raw("raw-bytes", [68, 32, 130, 60, 253, 230, 241, 194, 107, 48, 249, 14, 199, 221, 1, 228, 136, 117, 52, 162, 15, 11, 13, 4, 195, 110, 216, 14, 113, 224, 253, 119, 176, 118, 112, 235, 148, 11, 213, 51, 95, 151, 61, 170, 216, 97, 155, 145, 255, 201, 17, 245, 124, 206, 212, 88, 187, 191, 44, 224, 55, 83, 201, 189, 250, 15, 240, 22, 157, 201, 87, 86, 116, 6, 102, 118, 207, 176, 180, 235, 137, 2, 196, 66, 105, 218, 28, 246, 186, 102, 211, 248, 182, 212, 177, 0, 169, 234, 14, 117, 90, 92, 46, 130, 16, 36, 42, 8, 231, 7, 143, 127, 137, 56, 94, 176, 148, 35, 85, 81, 130, 86, 139, 150, 232, 164, 254, 242, 58, 12, 159, 197, 175, 215, 96, 132, 55, 129, 107, 221, 10, 115, 9, 203, 74, 18, 82, 228, 218, 112, 230, 114, 15, 202, 164, 218, 30, 152, 64, 108, 24, 156, 36, 39, 158, 152, 81, 213, 129, 66, 4, 19, 111, 235, 87, 19, 193, 102, 177, 50, 105, 221, 99, 252, 53, 199, 151, 255, 8, 166, 205, 144, 9, 80, 102, 167, 69, 173, 219, 109, 136, 49, 194, 176, 248, 120, 33, 20, 43, 68, 86, 85, 109, 137, 170, 130, 188, 173, 174, 58, 149, 120, 250, 69, 53, 164, 20, 208, 37, 194, 75, 64, 174, 58, 193, 39, 114, 41, 136, 186, 151, 58, 234, 141, 55, 23, 151, 6, 7, 46, 211, 58, 20, 96, 122, 215, 82, 59, 230, 85, 123, 81, 52, 222, 193, 150, 129, 244, 161, 51, 106, 162, 20, 13, 5, 151, 163, 230, 200, 160, 204, 32, 32, 162, 233, 57, 128, 110, 240, 182, 132, 93, 106, 157, 101, 126, 184, 41, 143, 45, 229, 46, 173, 116, 199, 157, 21, 167, 95, 162, 155, 125, 171, 51, 47, 125, 112, 10, 124, 205, 37, 137, 36, 38, 11, 5, 148, 183, 252, 240, 78, 51, 167, 39, 88, 91, 76, 72, 163, 156, 54, 150, 64, 105, 72, 16, 161, 105, 91, 153, 221, 80, 24, 126, 129, 32, 228, 220, 128, 224, 232, 5, 202, 173, 87, 132, 248, 12, 213, 9, 31, 181, 70, 64, 70, 132, 141, 203, 205, 88, 45, 119, 248, 3, 90, 162, 224, 115, 122, 160, 253, 245, 115, 211, 172, 140, 112, 24, 36, 188, 81, 104, 159, 152, 153, 190, 84, 237, 43, 63, 193, 90, 79, 128, 218, 111, 26, 253, 201, 178, 196, 84, 20, 46, 130, 51, 136, 42, 71, 41, 227, 123, 195, 221, 203, 84, 166, 224, 64, 249, 108, 61, 220, 209, 60, 151, 142, 127, 193, 2, 97, 224, 10, 15, 124, 133, 105, 88, 145, 75, 102, 139, 159, 128, 228, 86, 182, 251, 215, 62, 106, 196, 104, 145, 55, 12, 60, 6, 151, 69, 38, 191, 159, 223, 182, 165, 0, 63, 226, 230, 179, 156, 204, 173, 252, 57, 193, 195, 104, 1, 142, 101, 236, 209, 156, 87, 230, 101, 184, 1, 199, 218, 207, 172, 34, 252, 126, 148, 10, 208, 79, 203, 138, 91, 37, 5, 178, 135, 210, 155, 77, 236, 132, 248, 86, 239, 23, 138, 50, 216, 35, 181, 34, 226, 10, 84, 82, 47, 205, 141, 155, 106, 106, 121, 170, 137, 35, 38, 188, 239, 25, 86, 152, 138, 182, 118, 200, 204, 88, 247, 132, 168, 113, 132, 125, 15, 206, 162, 221, 127, 137, 97, 37, 84, 227, 75, 134, 235, 83, 70, 70, 225, 184, 158, 205, 123, 59, 105, 156, 34, 54, 116, 203, 164, 252, 51, 95, 23, 28, 11, 110, 17, 253, 226, 175, 140, 60, 88, 48, 113, 204, 119, 253, 230, 193, 86, 118, 120, 145, 236, 199, 108, 231, 132, 169, 254, 56, 109, 40, 23, 7, 2, 245, 163, 196, 147, 100, 204, 81, 77, 15, 7, 198, 74, 29, 194, 130, 66, 40, 236, 155, 7, 18, 31, 66, 21, 140, 60, 221, 46, 97, 14, 255, 66, 142, 98, 229, 199, 168, 137, 133, 124, 125, 30, 89, 179, 219, 31, 180, 211, 102, 217, 35, 136, 37, 128, 90, 49, 77, 30, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], "184f224f7ba487a424e318bfd4e1839187c9613194af32ba3f1eeeb344114e8a") <>
  Nil{}

def fails.put(n: String, +g: String, +w: String, +rest: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(g, w), rest,
    ("FAIL " ++ n ++ "\n  got:  " ++ g ++ "\n  want: " ++ w) <> rest)

def fails.at(+c: Case, rest: List<&2, String>) -> List<&2, String>:
  match c:
    case Case{n, +g, +w}:
      fails.put(n, g, w, rest)

def fails(cs: List<&2, Case>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      fails.at(c, fails(t))

def main() -> IO(Unit):
  +cs = cases()
  +n = List.length(&2, Case, cs)
  +fs = fails(cs)
  +f = List.length(&2, String, fs)
  do IO<Unit>:
    List.for_each(~&2, ~String, ~IO.print, fs)
    IO.print("sha256: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
