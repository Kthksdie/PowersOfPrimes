using PowersOfPrimes.Components;
using PowersOfPrimes.Extensions;
using System.Buffers.Text;
using System.Diagnostics;
using System.Numerics;
using System.Reflection;

namespace PowersOfPrimes {
    internal class Program {
        public static string DirectoryName = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);

        public static string DataFolder = $"{DirectoryName}\\Data";
        public static string ExponentsFolder = $"{DirectoryName}\\Data\\Exponents";
        public static string PrimesFolder = $"{DirectoryName}\\Data\\Primes";

        private static ConsoleColor _defaultFontColor = ConsoleColor.DarkGray;

        static void Main(string[] args) {
            Console.Title = "Prime Numbers";
            Console.CursorVisible = false;
            Console.ForegroundColor = _defaultFontColor;

            Testing();
            //Execute();

            Prompt();
        }

        public static void Testing() {
            var primeExponents = new List<BigInteger>();

            var testedCount = BigInteger.Zero;

            var positiveCount = BigInteger.Zero;
            foreach (var powerOf in Numberality.PowersOf(3, 0)) {
                if (!powerOf.IsPrimeExponent()) {
                    continue;
                }

                var multiplier = new BigInteger(2);
                var canidate = (powerOf.Value + 1) / (powerOf.Base + 1);
                var details = $"{powerOf.Base}^{powerOf.Exponent}+1/{(powerOf.Base + 1)}";

                //var canidate = (powerOf.Value - 1) / (powerOf.Base - 1);
                //var details = $"{powerOf.Base}^{powerOf.Exponent}-1/{(powerOf.Base - 1)}";

                //var canidate = powerOf.Value - (powerOf.Base - 1);
                //var details = $"{powerOf.Base}^{powerOf.Exponent}-{(powerOf.Base - 1)}";

                var numOfDigits = canidate.NumberOfDigits();
                //Print(0, $" {details} | digits {numOfDigits} | Tested {testedCount} | Positive {positiveCount}");
                //Print(1, $" {details} | {string.Join(", ", primeExponents)}");

                //Print($" {details}");

                if (CheckPrimalityAlt(canidate, powerOf.Base, powerOf.Exponent)) {
                    if (!primeExponents.Contains(powerOf.Exponent)) {
                        primeExponents.Add(powerOf.Exponent);
                    }

                    //Print($" {details} | digits {numOfDigits} | {canidate}", ConsoleColor.Blue);

                    // Check for any False Positives
                    if (canidate.IsProbablyPrime()) {
                        Print($" {details} | digits {numOfDigits} | {canidate}", ConsoleColor.Blue);
                    }
                    else {
                        // False Positive
                        Print($" {details} | digits {numOfDigits} | {canidate}", ConsoleColor.DarkRed);
                    }

                    //Prompt();
                }
                else {
                    //Print($" {details} | digits {numOfDigits} | {canidate}");

                    // Check for any False Negitives
                    if (canidate.IsProbablyPrime()) {
                        // False Negitive
                        Print($" {details} | digits {numOfDigits} | {canidate}", ConsoleColor.DarkGreen);
                    }
                    else {
                        Print($" {details} | digits {numOfDigits} | {canidate}");

                        var doubleE = powerOf.Exponent * multiplier;
                        var integerSqrt = canidate.IntegerSqrt();
                        foreach (var derivedPrime in Numberality.DerivedPrimeNumbers(powerOf.Exponent, multiplier, probablyPrime: true)) {
                            if (canidate % derivedPrime == 0) {
                                var i = derivedPrime / doubleE;

                                Print($"   i {i} | k {doubleE} | de {derivedPrime}");
                                break;
                            }

                            if (derivedPrime > integerSqrt) {
                                break;
                            }
                        }
                    }
                }

                Prompt();
                testedCount++;
            }

            static bool CheckPrimalityAlt(BigInteger canidate, BigInteger baseOf, BigInteger exponent) {
                if (canidate <= 0) {
                    return false;
                }

                var a = new BigInteger(2);
                if (baseOf == 2) {
                    a = new BigInteger(3);
                }

                //var a = baseOf - 1; // works?
                //var a = exponent - baseOf; // works?

                var b = BigInteger.Pow(a, (int)baseOf);
                //if (b > canidate) {
                //    return false; // Too small for this method, but may be prime.
                //}

                var s = b;
                for (int i = 0; i < exponent - 1; i++) {
                    s = BigInteger.ModPow(s, baseOf, canidate);
                }

                if (s == b) {
                    return true; // Prime
                }

                return false; // Composite
            }
        }

        public static void Execute() {
            var checkWatch = new Stopwatch();

            var primeExponents = new List<BigInteger>();

            var testedCount = BigInteger.Zero;
            var positiveCount = BigInteger.Zero;

            // I'm skipping double validating with Probable check.
            // Results are already in OEIS for the numbers we're checking, will cross reference anyway.
            var falsePositiveCount = BigInteger.Zero;
            var falseNegitiveCount = BigInteger.Zero;

            foreach (var powerOf in Numberality.PowersOf(3, 0)) {
                //if (!powerOf.IsPrimeExponent()) {
                //    continue;
                //}

                //var canidate = (powerOf.Value - 1) / (powerOf.Base - 1);
                //var details = $"{powerOf.Base}^{powerOf.Exponent}/{(powerOf.Base - 1)}";

                var canidate = powerOf.Value - (powerOf.Base - 1);
                var details = $"{powerOf.Base}^{powerOf.Exponent}-{(powerOf.Base - 1)}";

                var numOfDigits = canidate.NumberOfDigits();
                Print(0, $" {details} | Digits {numOfDigits} | Tested {testedCount} | Positive {positiveCount}");
                Print(1, $" {details} | {string.Join(", ", primeExponents)}");

                checkWatch.Restart();

                if (canidate.CheckPrimality(powerOf.Base, powerOf.Exponent)) {
                    checkWatch.Stop();

                    if (!primeExponents.Contains(powerOf.Exponent)) {
                        primeExponents.Add(powerOf.Exponent);
                    }

                    Print(5, $" {details} | Digits {numOfDigits} | {checkWatch.Elapsed}", ConsoleColor.Blue);
                    positiveCount++;

                    //Save(details, canidate);
                }
                else {
                    checkWatch.Stop();

                    Print(5, $" {details} | Digits {numOfDigits} | {checkWatch.Elapsed}");
                }

                //Prompt();
                testedCount++;
                if (testedCount > 5000) {
                    break;
                }
            }
        }

        public static void Save(BigInteger baseOf, BigInteger exponent, BigInteger canidate) {
            var filePath = $"{PrimesFolder}\\{baseOf}^{exponent}.txt";

            if (!File.Exists(filePath)) {
                File.WriteAllText(filePath, canidate.ToString());
            }
        }

        public static void Save(string details, BigInteger canidate) {
            var filePath = $"{PrimesFolder}\\{details.Replace('/', 'd')}.txt";

            if (!File.Exists(filePath)) {
                File.WriteAllText(filePath, canidate.ToString());
            }
        }

        public static ConsoleKeyInfo Prompt() {
            return Console.ReadKey();
        }

        public static void Print(string message) {
            Console.WriteLine(message);
        }

        public static void Print(string message, ConsoleColor color) {
            Console.ForegroundColor = color;
            Console.WriteLine(message);
            Console.ForegroundColor = _defaultFontColor;
        }

        public static void Print(int row, string message) {
            Console.SetCursorPosition(0, row);
            ClearCurrentLine();

            Console.WriteLine(message);
        }

        public static void Print(int row, string message, ConsoleColor color) {
            Console.SetCursorPosition(0, row);
            ClearCurrentLine();

            Console.ForegroundColor = color;
            Console.WriteLine(message);
            Console.ForegroundColor = _defaultFontColor;
        }

        private static string _clearString = new string(' ', Console.BufferWidth);
        public static void ClearCurrentLine() {
            var currentCursorTop = Console.CursorTop;

            Console.SetCursorPosition(0, Console.CursorTop);
            Console.Write(_clearString);
            Console.SetCursorPosition(0, currentCursorTop);
        }
    }
}