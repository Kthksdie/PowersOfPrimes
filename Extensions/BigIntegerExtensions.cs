using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace PowersOfPrimes.Extensions {
    public static class BigIntegerExtensions {
        private static Random _random = new Random();

        public static BigInteger Next(this Random random, BigInteger minValue, BigInteger maxValue) {
            // Returns a random BigInteger that is within a specified range.
            // The lower bound is inclusive, and the upper bound is exclusive.
            // https://stackoverflow.com/a/68593532 - Theodor Zoulias

            if (minValue > maxValue) {
                throw new ArgumentException();
            }
            else if (minValue == maxValue) {
                return minValue;
            }

            var zeroBasedUpperBound = maxValue - 1 - minValue; // Inclusive
            var bytes = zeroBasedUpperBound.ToByteArray();
            var lastByteMask = (byte)0b11111111; // Search for the most significant non-zero bit
            for (var mask = (byte)0b10000000; mask > 0; mask >>= 1, lastByteMask >>= 1) {
                if ((bytes[bytes.Length - 1] & mask) == mask) {
                    break; // We found it
                }
            }

            var result = BigInteger.Zero;
            while (true) {
                random.NextBytes(bytes);

                bytes[bytes.Length - 1] &= lastByteMask;

                result = new BigInteger(bytes);

                if (result <= zeroBasedUpperBound) {
                    return result + minValue;
                }
            }
        }

        public static bool IsProbablyPrime(this BigInteger n, int certainty = 8) {
            // https://rosettacode.org/wiki/Miller%E2%80%93Rabin_primality_test#C#
            // Added different random gen method.

            if (n <= 1) {
                return false;
            }

            if (n == 2 || n == 3) {
                return true;
            }

            if (n.IsEven) {
                return false;
            }

            var nMinusOne = n - 1;
            var nMinusTwo = n - 2;

            var d = nMinusOne;
            int s = 0;

            while (d % 2 == 0) {
                d /= 2;
                s += 1;
            }

            BigInteger a, x;
            for (int i = 0; i < certainty; i++) {
                a = _random.Next(2, nMinusTwo);

                x = BigInteger.ModPow(a, d, n);
                if (x == 1 || x == nMinusOne) {
                    continue;
                }

                for (int r = 1; r < s; r++) {
                    x = BigInteger.ModPow(x, 2, n);

                    if (x == 1) {
                        return false;
                    }

                    if (x == nMinusOne) {
                        break;
                    }
                }

                if (x != nMinusOne) {
                    return false;
                }
            }

            return true;
        }

        public static BigInteger IntegerSqrt(this BigInteger n) {
            // https://github.com/SunsetQuest/NewtonPlus-Fast-BigInteger-and-BigFloat-Square-Root

            if (n < 144838757784765629) { // 1.448e17 = ~1<<57
                uint vInt = (uint)Math.Sqrt((ulong)n);

                if (n <= 4503599761588224 && (ulong)vInt * vInt > (ulong)n) { // 4.5e15 = ~1<<52
                    vInt--;
                }

                return vInt;
            }

            double xAsDub = (double)n;
            if (xAsDub < 8.5e37) { // 8.5e37 is V<sup>2</sup>long.max * long.max
                ulong vInt = (ulong)Math.Sqrt(xAsDub);
                BigInteger v = vInt + (ulong)(n / vInt) >> 1;
                return v * v >= n ? v : v - 1;
            }

            if (xAsDub < 4.3322e127) {
                BigInteger v = (BigInteger)Math.Sqrt(xAsDub);
                v = v + n / v >> 1;
                if (xAsDub > 2e63) {
                    v = v + n / v >> 1;
                }
                return v * v >= n ? v : v - 1;
            }

            int xLen = (int)n.GetBitLength();
            int wantedPrecision = (xLen + 1) / 2;
            int xLenMod = xLen + (xLen & 1) + 1;

            // Do the first Sqrt on hardware
            long tempX = (long)(n >> xLenMod - 63);
            double tempSqrt1 = Math.Sqrt(tempX);
            ulong valLong = (ulong)BitConverter.DoubleToInt64Bits(tempSqrt1) & 0x1fffffffffffffL;
            if (valLong == 0) {
                valLong = 1UL << 53;
            }

            // Classic Newton Iterations
            BigInteger val = ((BigInteger)valLong << 53 - 1) + (n >> xLenMod - 3 * 53) / valLong;
            int size = 106;
            for (; size < 256; size <<= 1) {
                val = (val << size - 1) + (n >> xLenMod - 3 * size) / val;
            }

            if (xAsDub > 4e254) { // 1 << 845
                int numOfNewtonSteps = BitOperations.Log2((uint)(wantedPrecision / size)) + 2;

                // Apply Starting Size
                int wantedSize = (wantedPrecision >> numOfNewtonSteps) + 2;
                int needToShiftBy = size - wantedSize;
                val >>= needToShiftBy;
                size = wantedSize;
                do {
                    // Newton Plus Iterations

                    int shiftX = xLenMod - 3 * size;
                    BigInteger valSqrd = val * val << size - 1;
                    BigInteger valSU = (n >> shiftX) - valSqrd;
                    val = (val << size) + valSU / val;
                    size *= 2;
                } while (size < wantedPrecision);
            }

            // There are a few extra digits here, lets save them
            int oversidedBy = size - wantedPrecision;
            BigInteger saveDroppedDigitsBI = val & (BigInteger.One << oversidedBy) - 1;
            int downby = oversidedBy < 64 ? (oversidedBy >> 2) + 1 : oversidedBy - 32;
            ulong saveDroppedDigits = (ulong)(saveDroppedDigitsBI >> downby);

            // Shrink result to wanted Precision
            val >>= oversidedBy;

            // Detect a round-ups
            if (saveDroppedDigits == 0 && val * val > n) {
                val--;
            }

            // //////// Error Detection ////////
            // // I believe the above has no errors but to guarantee the following can be added.
            // // If an error is found, please report it.
            // BigInteger tmp = val * val;
            // if (tmp > x)
            // {
            //     throw new Exception("Sqrt function had internal error - value too high");
            // }
            // if ((tmp + 2 * val + 1) >= x)
            // {
            //     throw new Exception("Sqrt function had internal error - value too low");
            // }

            return val;
        }
    }
}
