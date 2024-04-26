using PowersOfPrimes.Extensions;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace PowersOfPrimes.Components {
    public static class Numberality {
        public static IEnumerable<PowerOf> PowersOf(BigInteger baseOf, BigInteger targetExponent) {
            if (baseOf == 1) {
                baseOf = 2;
            }

            var powerOf = new PowerOf(baseOf, 0, 1);

            while (powerOf.Exponent < targetExponent) {
                powerOf.Value *= baseOf;
                powerOf.Exponent++;
            }

            while (true) {
                yield return powerOf;

                powerOf.Value *= baseOf;
                powerOf.Exponent++;
            }
        }

        public static bool IsPowerOf(this BigInteger n, BigInteger baseOf) {
            if (n == 0) {
                return false;
            }

            while (n % baseOf == 0) {
                n /= baseOf;
            }

            return n == 1;
        }

        public static int GreatestExponentOf(this BigInteger n, BigInteger power) {
            if (n <= 0) {
                return 0;
            }

            var exponent = -1;
            var powerOf = BigInteger.One;

            while (true) {
                if (n % powerOf == 0) {
                    powerOf *= power;
                    exponent++;
                }
                else {
                    break;
                }
            }

            return exponent;
        }

        public static BigInteger GreatestMultipleOf(this BigInteger n, BigInteger multiple) {
            if (n <= 0) {
                return 0;
            }

            var multipleOf = multiple;

            while (true) {
                if (n % (multipleOf + multipleOf) == 0) {
                    multipleOf += multipleOf;
                }
                else {
                    break;
                }

            }

            return multipleOf;
        }

        public static BigInteger LastDigit(this BigInteger n) {
            return n % 10;
        }

        public static int NumberOfDigits(this BigInteger n) {
            if (n == 0) {
                return 1;
            }

            if (n < 0) {
                n = n * -1;
            }

            return (int)Math.Floor(BigInteger.Log10(n) + 1);
        }

        /// <summary>
        /// <para>Method inspired by Lucas-Lehmer's for 2^p - 1, and by Alan Gee's for (3^p - 1)/2.</para>
        /// <para>Works for:</para>
        /// <para>(k^n) - (k - 1)</para>
        /// <para>(k^p - 1)/k - 1    *k cannot be p^n; where n > 1*</para>
        /// <para>@JKthksdie</para>
        /// </summary>
        public static bool CheckPrimality(this BigInteger canidate, BigInteger baseOf, BigInteger exponent) {
            if (canidate <= 0) {
                return false;
            }

            var a = new BigInteger(2);
            if (baseOf == 2) {
                a = new BigInteger(3);
            }

            var v = BigInteger.Pow(a, (int)baseOf);
            if (v > canidate) {
                return false; // Too small for this method, but may be prime.
            }

            var s = v;
            for (int i = 0; i < exponent - 1; i++) {
                s = BigInteger.ModPow(s, baseOf, canidate);
            }

            if (s == v) {
                return true; // Prime
            }

            return false; // Composite
        }

        /// <summary>
        /// <para>Only for (k^p-1)/k-1 *k cannot be a power of 2*</para>
        /// <para>@JKthksdie</para>
        /// </summary>
        /// <param name="canidate"></param>
        /// <param name="baseOf"></param>
        /// <param name="primeExponent"></param>
        /// <returns></returns>
        /// <exception cref="ArgumentException"></exception>
        public static bool IsPrimeOfPower(this BigInteger canidate, BigInteger baseOf, BigInteger primeExponent) {
            if (baseOf.IsPowerOfTwo) {
                throw new ArgumentException($"baseOf cannot be a power of 2.");
            }

            var d = canidate / primeExponent;
            var x = BigInteger.ModPow(2, d, canidate);
            if (x.IsPowerOf(baseOf)) { // || x == 1
                return true;
            }

            return false;
        }

        /// <summary>
        /// <para>Only for 2^p-1</para>
        /// <para>@JKthksdie</para>
        /// </summary>
        /// <param name="canidate"></param>
        /// <param name="primeExponent"></param>
        /// <returns></returns>
        public static bool IsMersennePrime(this BigInteger canidate, BigInteger primeExponent) {
            BigInteger d, x;

            var lastDigit = canidate % 10;
            if (lastDigit == 1) {
                d = (canidate / (primeExponent * 2));
                x = BigInteger.ModPow(5, d, canidate);

                if (x.IsPowerOfTwo) {
                    return true;
                }

                return false;
            }

            d = (canidate / primeExponent);
            x = BigInteger.ModPow(3, d, canidate);

            if (x.IsPowerOfTwo) {
                return true;
            }

            return false;
        }

        /// <summary>
        /// Lucas-Lehmer method for primes in the form 2^p-1
        /// </summary>
        /// <param name="canidate"></param>
        /// <param name="primeExponent"></param>
        /// <returns></returns>
        public static bool CheckLucasLehmerPrimality(this BigInteger canidate, BigInteger primeExponent) {
            var s = new BigInteger(4);
            for (BigInteger i = 0; i < primeExponent - 2; i++) {
                s = BigInteger.ModPow(s, 2, canidate) - 2;
            }

            if (s == 0) {
                return true; // Prime
            }

            return false; // Composite
        }

        /// <summary>
        /// <para>Alan Gee method for primes in the form (3^p-1)/2</para>
        /// <para>ref: https://math.stackexchange.com/a/2422592 - Alan Gee | (https://math.stackexchange.com/users/43196/alan-gee)</para>
        /// </summary>
        /// <param name="canidate"></param>
        /// <param name="primeExponent"></param>
        /// <returns></returns>
        public static bool CheckAlanGeePrimality(this BigInteger canidate, BigInteger primeExponent) {
            var s = new BigInteger(8);
            for (BigInteger i = 0; i < primeExponent - 1; i++) {
                s = BigInteger.ModPow(s, 3, canidate);
            }

            if (s == 8) {
                return true; // Prime
            }

            return false; // Composite
        }

        public static IEnumerable<BigInteger> DerivedPrimeNumbers(BigInteger primeExponent, BigInteger multiplier, bool probablyPrime = true) {
            var derivedPrime = BigInteger.Zero;

            var k = primeExponent * multiplier;
            var multipleK = k;

            //var k2 = primeExponent * (multiplier * 2);
            //var multipleK2 = k2;

            while (true) {
                derivedPrime = multipleK + 1;
                if (probablyPrime) {
                    if (derivedPrime.IsProbablyPrime(1)) {
                        yield return derivedPrime;
                    }
                }
                else {
                    yield return derivedPrime;
                }

                //derivedPrime = multipleK2 + 1;
                //if (probablyPrime) {
                //    if (derivedPrime.IsProbablyPrime(1)) {
                //        yield return derivedPrime;
                //    }
                //}
                //else {
                //    yield return derivedPrime;
                //}

                multipleK += k;
                //multipleK2 += k2;
            }
        }

        public static List<BigInteger> Divisors(this BigInteger canidate) {
            var divisors = new List<BigInteger>();

            var integerSqrt = canidate.IntegerSqrt();

            var boundary = integerSqrt + (integerSqrt >> 1);
            for (BigInteger d = 2; d < boundary; d++) {
                if (canidate % d == 0) {
                    divisors.Add(d);
                }
            }

            return divisors;
        }
    }
}
