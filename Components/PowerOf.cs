using PowersOfPrimes.Extensions;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace PowersOfPrimes.Components {
    public class PowerOf {
        public BigInteger Base;

        public BigInteger Exponent;

        public BigInteger Value;

        public PowerOf(BigInteger baseOf, BigInteger exponent, BigInteger value) {
            Base = baseOf;
            Exponent = exponent;
            Value = value;
        }

        public bool IsPrimeExponent() {
            if (Exponent.IsProbablyPrime()) {
                return true;
            }

            return false;
        }
    }
}
