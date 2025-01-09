use core::debug::PrintTrait;
use core::option::OptionTrait;
use core::result::{ResultTrait, ResultTraitImpl};
use core::traits::{Into, TryInto};
use core::ops::{AddAssign, SubAssign, MulAssign, DivAssign};
use core::integer::{u256_safe_div_rem, u256_as_non_zero, upcast};
use core::integer;
use core::num::traits::{Sqrt, WideMul};
use crate::f256::math::lut;
use crate::f256::types::fixed::{
    HALF_u256, MAX_u256, ONE_u256, Fixed, FixedInto, FixedTrait, FixedAdd, FixedDiv, FixedMul,
    FixedNeg,
};

// PUBLIC

fn abs(a: Fixed) -> Fixed {
    return FixedTrait::new(a.mag, false);
}

fn add(a: Fixed, b: Fixed) -> Fixed {
    if a.sign == b.sign {
        return FixedTrait::new(a.mag + b.mag, a.sign);
    }

    if a.mag == b.mag {
        return FixedTrait::ZERO();
    }

    if (a.mag > b.mag) {
        return FixedTrait::new(a.mag - b.mag, a.sign);
    } else {
        return FixedTrait::new(b.mag - a.mag, b.sign);
    }
}

fn ceil(a: Fixed) -> Fixed {
    let (div_u256, rem_u256) = _split_unsigned(a);

    if rem_u256 == 0 {
        return a;
    } else if !a.sign {
        return FixedTrait::new_unscaled(div_u256 + 1, false);
    } else if div_u256 == 0 {
        return FixedTrait::new_unscaled(0, false);
    } else {
        return FixedTrait::new_unscaled(div_u256, true);
    }
}

fn div(a: Fixed, b: Fixed) -> Fixed {
    let a_u256 = WideMul::wide_mul(a.mag, ONE_u256);
    let (res_u256, _) = integer::u512_safe_div_rem_by_u256(a_u256, b.mag.try_into().unwrap());

    assert((res_u256.limb2 == 0) && (res_u256.limb3 == 0), 'result overflow');

    // Re-apply sign
    return FixedTrait::new(u256 { low: res_u256.limb0, high: res_u256.limb1 }, a.sign ^ b.sign);
}

fn eq(a: @Fixed, b: @Fixed) -> bool {
    return (*a.mag == *b.mag) && (*a.sign == *b.sign);
}

// Calculates the natural exponent of x: e^x
fn exp(a: Fixed) -> Fixed {
    return exp2(FixedTrait::new(490923683258796565755804390113247494144, false) * a);
}

// Calculates the binary exponent of x: 2^x
fn exp2(a: Fixed) -> Fixed {
    if (a.mag == 0) {
        return FixedTrait::ONE();
    }

    let (int_part, frac_part) = _split_unsigned(a);
    let int_res = FixedTrait::new_unscaled(lut::exp2(int_part), false);
    let mut res_u = int_res;

    if frac_part != 0 {
        let frac_fixed = FixedTrait::new(frac_part, false);
        let r8 = FixedTrait::new(769080727072485422853988418584576, false) * frac_fixed;
        let r7 = (r8 + FixedTrait::new(4276284773707043248098818222194688, false)) * frac_fixed;
        let r6 = (r7 + FixedTrait::new(53714623828716100340108848594419712, false)) * frac_fixed;
        let r5 = (r6 + FixedTrait::new(452676417907555097514849187053699072, false)) * frac_fixed;
        let r4 = (r5 + FixedTrait::new(3273365328756154879537193328205365248, false)) * frac_fixed;
        let r3 = (r4 + FixedTrait::new(18886940937204083031619808925633740800, false)) * frac_fixed;
        let r2 = (r3 + FixedTrait::new(81744862027718483807109747266820243456, false)) * frac_fixed;
        let r1 = (r2 + FixedTrait::new(235865762211548639247464659276563218432, false))
            * frac_fixed;
        res_u = res_u * (r1 + FixedTrait::ONE());
    }

    if (a.sign == true) {
        return FixedTrait::ONE() / res_u;
    } else {
        return res_u;
    }
}

fn exp2_int(exp: u256) -> Fixed {
    return FixedTrait::new_unscaled(lut::exp2(exp), false);
}

fn floor(a: Fixed) -> Fixed {
    let (div_u256, rem_u256) = _split_unsigned(a);

    if rem_u256 == 0 {
        return a;
    } else if !a.sign {
        return FixedTrait::new_unscaled(div_u256, false);
    } else {
        return FixedTrait::new_unscaled(div_u256 + 1, true);
    }
}

fn ge(a: Fixed, b: Fixed) -> bool {
    if a.sign != b.sign {
        return !a.sign;
    } else {
        return (a.mag == b.mag) || ((a.mag > b.mag) ^ a.sign);
    }
}

fn gt(a: Fixed, b: Fixed) -> bool {
    if a.sign != b.sign {
        return !a.sign;
    } else {
        return (a.mag != b.mag) && ((a.mag > b.mag) ^ a.sign);
    }
}

fn le(a: Fixed, b: Fixed) -> bool {
    if a.sign != b.sign {
        return a.sign;
    } else {
        return (a.mag == b.mag) || ((a.mag < b.mag) ^ a.sign);
    }
}

// Calculates the natural logarithm of x: ln(x)
// self must be greater than zero
fn ln(a: Fixed) -> Fixed {
    return FixedTrait::new(235865763225513294141843218151044546560, false)
        * log2(a); // ln(2) = 0.693...
}

// Calculates the binary logarithm of x: log2(x)
// self must be greather than zero
fn log2(a: Fixed) -> Fixed {
    assert(a.sign == false, 'must be positive');

    if (a.mag == ONE_u256) {
        return FixedTrait::ZERO();
    } else if (a.mag < ONE_u256) {
        // Compute true inverse binary log if 0 < x < 1
        let div = FixedTrait::ONE() / a;
        return -log2(div);
    }

    let (msb, div) = lut::msb(a.mag / ONE_u256);
    let norm = a / FixedTrait::new_unscaled(div, false);

    let r8 = FixedTrait::new(3092796470289144265053198215716798464, true) * norm;
    let r7 = (r8 + FixedTrait::new(42142524430293287633097644348712943616, false)) * norm;
    let r6 = (r7 + FixedTrait::new(254652914610607944976177913259976818688, true)) * norm;
    let r5 = (r6 + FixedTrait::new(897928449586886277058785639754262118400, false)) * norm;
    let r4 = (r5 + FixedTrait::new(2046265499274736149768238433130814373888, true)) * norm;
    let r3 = (r4 + FixedTrait::new(3159856979795512482444907416790102966272, false)) * norm;
    let r2 = (r3 + FixedTrait::new(3405252005575274618856263264032736149504, true)) * norm;
    let r1 = (r2 + FixedTrait::new(2774936165944314964447787733260936675328, false)) * norm;
    return r1
        + FixedTrait::new(1165600889421153703778965674399245533184, true)
        + FixedTrait::new_unscaled(msb, false);
}

// Calculates the base 10 log of x: log10(x)
// self must be greater than zero
fn log10(a: Fixed) -> Fixed {
    return FixedTrait::new(102435199438739363744840660942755725312, false)
        * log2(a); // log10(2) = 0.301...
}

fn lt(a: Fixed, b: Fixed) -> bool {
    if a.sign != b.sign {
        return a.sign;
    } else {
        return (a.mag != b.mag) && ((a.mag < b.mag) ^ a.sign);
    }
}

fn mul(a: Fixed, b: Fixed) -> Fixed {
    let res_u256 = WideMul::wide_mul(a.mag, b.mag);
    let (scaled_u256, _) = integer::u512_safe_div_rem_by_u256(res_u256, u256_as_non_zero(ONE_u256));

    assert((scaled_u256.limb2 == 0) && (scaled_u256.limb3 == 0), 'result overflow');

    // Re-apply sign
    return FixedTrait::new(
        u256 { low: scaled_u256.limb0, high: scaled_u256.limb1 }, a.sign ^ b.sign,
    );
}

#[derive(Copy, Drop, Serde, Debug)]
struct f64 {
    mag: u64,
    sign: bool,
}

fn mul_64(a: f64, b: f64) -> f64 {
    let prod_u256 = WideMul::wide_mul(a.mag, b.mag);
    return f64 { mag: (prod_u256 / 4294967296).try_into().unwrap(), sign: a.sign ^ b.sign };
}

fn ne(a: @Fixed, b: @Fixed) -> bool {
    return (*a.mag != *b.mag) || (*a.sign != *b.sign);
}

fn neg(a: Fixed) -> Fixed {
    if a.mag == 0 {
        return a;
    } else if !a.sign {
        return FixedTrait::new(a.mag, !a.sign);
    } else {
        return FixedTrait::new(a.mag, false);
    }
}

// Calclates the value of x^y and checks for overflow before returning
// self is a fixed point value
// b is a fixed point value
fn pow(a: Fixed, b: Fixed) -> Fixed {
    let (_div_u256, rem_u256) = _split_unsigned(b);

    // use the more performant integer pow when y is an int
    if (rem_u256 == 0) {
        return pow_int(a, b.mag / ONE_u256, b.sign);
    }

    // x^y = exp(y*ln(x)) for x > 0 will error for x < 0
    return exp(b * ln(a));
}

// Calclates the value of a^b and checks for overflow before returning
fn pow_int(a: Fixed, b: u256, sign: bool) -> Fixed {
    let mut x = a;
    let mut n = b;

    if sign == true {
        x = FixedTrait::ONE() / x;
    }

    if n == 0 {
        return FixedTrait::ONE();
    }

    let mut y = FixedTrait::ONE();
    let two = integer::u256_as_non_zero(2);

    loop {
        if n <= 1 {
            break;
        }

        let (div, rem, _guarantee) = integer::u256_safe_divmod(n, two);

        if rem == 1 {
            y = x * y;
        }

        x = x * x;
        n = div;
    };

    return x * y;
}

fn rem(a: Fixed, b: Fixed) -> Fixed {
    return a - floor(a / b) * b;
}

fn round(a: Fixed) -> Fixed {
    let (div_u256, rem_u256) = _split_unsigned(a);

    if (HALF_u256 <= rem_u256) {
        return FixedTrait::new(ONE_u256 * (div_u256 + 1), a.sign);
    } else {
        return FixedTrait::new(ONE_u256 * div_u256, a.sign);
    }
}

// Calculates the square root of a fixed point value
// x must be positive
fn sqrt(a: Fixed) -> Fixed {
    assert(a.sign == false, 'must be positive');
    let root = a.mag.sqrt();
    let scale_root = ONE_u256.sqrt();
    let res_u256 = root.into() * ONE_u256 / scale_root.into();
    return FixedTrait::new(res_u256, false);
}

fn sub(a: Fixed, b: Fixed) -> Fixed {
    return add(a, -b);
}

// Ignores sign and always returns false
fn _split_unsigned(a: Fixed) -> (u256, u256) {
    let (div, rem, _) = integer::u256_safe_divmod(a.mag, integer::u256_as_non_zero(ONE_u256));
    return (div, rem);
}

// Tests
// --------------------------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::f256::test::helpers::assert_precise;
    use crate::f256::types::fixed::{
        ONE, HALF, FixedPartialEq, FixedPartialOrd, FixedAddAssign, FixedSub, FixedSubAssign,
        FixedMulAssign,
    };

    use crate::f256::math::trig::HALF_PI_u256;
    use crate::f256::math::trig::PI_u256;
    use core::integer;
    use super::{FixedTrait, ONE_u256, lut, exp2_int};

    #[test]
    fn test_into() {
        let a = FixedTrait::from_unscaled_felt(5);
        assert(a.try_into().unwrap() == 5 * ONE, 'invalid result');
    }

    #[test]
    fn test_try_into_u256() {
        // Positive unscaled
        let a = FixedTrait::new_unscaled(5, false);
        assert(a.try_into().unwrap() == 5_u256, 'invalid result');

        // Positive scaled
        let b = FixedTrait::new(5 * ONE_u256, false);
        assert(b.try_into().unwrap() == 5_u256, 'invalid result');

        let c = FixedTrait::new(PI_u256, false);
        assert(c.try_into().unwrap() == 3_u256, 'invalid result');

        // Zero
        let d = FixedTrait::new_unscaled(0, false);
        assert(d.try_into().unwrap() == 0_u256, 'invalid result');
    }

    #[test]
    #[should_panic]
    fn test_negative_try_into_u256() {
        let a = FixedTrait::new_unscaled(1, true);
        let _a: u256 = a.try_into().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_overflow_large() {
        let too_large = 0x100000000000000000000000000000000;
        FixedTrait::from_felt(too_large);
    }

    #[test]
    #[should_panic]
    fn test_overflow_small() {
        let too_small = -0x100000000000000000000000000000000;
        FixedTrait::from_felt(too_small);
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_acos() {
        let a = FixedTrait::ONE();
        assert(a.acos().try_into().unwrap() == 0, 'invalid one');
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_asin() {
        let a = FixedTrait::ONE();
        assert(a.asin().try_into().unwrap() == 28976077832308491370, 'invalid one'); // PI / 2
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_atan() {
        let a = FixedTrait::new(2 * ONE_u256, false);

        // use `DEFAULT_PRECISION`
        assert_precise(a.atan(), 20423289048683266000, 'invalid two', Option::None(()));

        // use `custom_precision`
        assert_precise(
            a.atan(), 20423289048683266000, 'invalid two', Option::Some(184467440737),
        ); // 1e-8
    }

    #[test]
    fn test_ceil() {
        let a = FixedTrait::from_felt(53495557813757699680); // 2.9
        assert(a.ceil().try_into().unwrap() == 3 * ONE, 'invalid pos decimal');
    }

    #[test]
    fn test_floor() {
        let a = FixedTrait::from_felt(53495557813757699680); // 2.9
        assert(a.floor().try_into().unwrap() == 2 * ONE, 'invalid pos decimal');
    }

    #[test]
    fn test_round() {
        let a = FixedTrait::from_felt(53495557813757699680); // 2.9
        assert(a.round().try_into().unwrap() == 3 * ONE, 'invalid pos decimal');
    }

    #[test]
    #[should_panic]
    fn test_sqrt_fail() {
        let a = FixedTrait::from_unscaled_felt(-25);
        a.sqrt();
    }

    #[test]
    fn test_sqrt() {
        let a = FixedTrait::from_unscaled_felt(0);
        assert(a.sqrt().try_into().unwrap() == 0, 'invalid zero root');
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_msb() {
        let a = FixedTrait::new_unscaled(4503599627370495, false);
        let (msb, div) = lut::msb(a.mag / ONE_u256);
        assert(msb == 51, 'invalid msb');
        assert(div == 2251799813685248, 'invalid msb ceil');
    }

    #[test]
    #[available_gas(100000000000)] // 260k
    fn test_pow() {
        let a = FixedTrait::new_unscaled(3, false);
        let b = FixedTrait::new_unscaled(4, false);
        assert(a.pow(b).try_into().unwrap() == 81 * ONE, 'invalid pos base power');
    }

    #[test]
    #[available_gas(100000000000)] // 550k
    fn test_pow_frac() {
        let a = FixedTrait::new_unscaled(3, false);
        let b = FixedTrait::new(9223372036854775808, false); // 0.5
        assert_precise(
            a.pow(b), 31950697969885030000, 'invalid pos base power', Option::None(()),
        ); // 1.7320508075688772
    }

    #[test]
    #[available_gas(100000000000)] // 267k
    fn test_exp() {
        let a = FixedTrait::new_unscaled(2, false);
        assert(
            a.exp().try_into().unwrap() == 2514365498609124591954379942667344435972,
            'invalid exp of 2',
        ); // 7.389056098793725
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_exp2() {
        let a = FixedTrait::new_unscaled(24, false);
        assert(
            a.exp2().try_into().unwrap() == 5708990770823839524233143877797980545530986496,
            'invalid exp2 of 2',
        );
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_exp2_int() {
        assert(
            exp2_int(24).try_into().unwrap() == 5708990770823839524233143877797980545530986496,
            'invalid exp2 of 2',
        );
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_ln() {
        let a = FixedTrait::from_unscaled_felt(1);
        assert(a.ln().try_into().unwrap() == 0, 'invalid ln of 1');
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_log2() {
        let a = FixedTrait::from_unscaled_felt(32);
        assert_precise(a.log2(), 5 * ONE, 'invalid log2 32', Option::None(()));
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_log10() {
        let a = FixedTrait::from_unscaled_felt(100);
        assert_precise(a.log10(), 2 * ONE, 'invalid log10', Option::None(()));
    }

    #[test]
    fn test_eq() {
        let a = FixedTrait::from_unscaled_felt(42);
        let b = FixedTrait::from_unscaled_felt(42);
        let c = a == b;
        assert(c == true, 'invalid result');
    }

    #[test]
    fn test_ne() {
        let a = FixedTrait::from_unscaled_felt(42);
        let b = FixedTrait::from_unscaled_felt(42);
        let c = a != b;
        assert(c == false, 'invalid result');
    }

    #[test]
    fn test_add() {
        let a = FixedTrait::from_unscaled_felt(1);
        let b = FixedTrait::from_unscaled_felt(2);
        assert(a + b == FixedTrait::from_unscaled_felt(3), 'invalid result');
    }

    #[test]
    fn test_add_eq() {
        let mut a = FixedTrait::from_unscaled_felt(1);
        let b = FixedTrait::from_unscaled_felt(2);
        a += b;
        assert(a.try_into().unwrap() == 3 * ONE, 'invalid result');
    }

    #[test]
    fn test_sub() {
        let a = FixedTrait::from_unscaled_felt(5);
        let b = FixedTrait::from_unscaled_felt(2);
        let c = a - b;
        assert(c.try_into().unwrap() == 3 * ONE, 'false result invalid');
    }

    #[test]
    fn test_sub_eq() {
        let mut a = FixedTrait::from_unscaled_felt(5);
        let b = FixedTrait::from_unscaled_felt(2);
        a -= b;
        assert(a.try_into().unwrap() == 3 * ONE, 'invalid result');
    }

    #[test]
    #[available_gas(100000000000)] // 22k
    fn test_mul_pos() {
        let a = FixedTrait::new(986818864070721543925727199480386682880, false); // 2.9
        let b = FixedTrait::new(986818864070721543925727199480386682880, false); // 2.9
        let c = a * b;
        assert(c.try_into().unwrap() == 2861774705805092477042237308485072102400, 'invalid result');
    }

    #[test]
    fn test_mul_neg() {
        let a = FixedTrait::from_unscaled_felt(5);
        let b = FixedTrait::from_unscaled_felt(-2);
        let c = a * b;
        assert(c.try_into().unwrap() == -10 * ONE, 'true result invalid');
    }

    #[test]
    fn test_mul_eq() {
        let mut a = FixedTrait::from_unscaled_felt(5);
        let b = FixedTrait::from_unscaled_felt(-2);
        a *= b;
        assert(a.try_into().unwrap() == -10 * ONE, 'invalid result');
    }

    #[test]
    fn test_div() {
        let a = FixedTrait::from_unscaled_felt(10);
        let b = FixedTrait::from_felt(53495557813757699680); // 2.9
        let c = a / b;
        assert(
            c.try_into().unwrap() == 63609462323136384890, 'invalid pos decimal',
        ); // 3.4482758620689653
    }

    #[test]
    fn test_le() {
        let a = FixedTrait::from_unscaled_felt(1);
        let b = FixedTrait::from_unscaled_felt(0);
        let c = FixedTrait::from_unscaled_felt(-1);

        assert(a <= a, 'a <= a');
        assert(!(a <= b), 'a <= b');
        assert(!(a <= c), 'a <= c');

        assert(b <= a, 'b <= a');
        assert(b <= b, 'b <= b');
        assert(!(b <= c), 'b <= c');

        assert(c <= a, 'c <= a');
        assert(c <= b, 'c <= b');
        assert(c <= c, 'c <= c');
    }

    #[test]
    fn test_lt() {
        let a = FixedTrait::from_unscaled_felt(1);
        let b = FixedTrait::from_unscaled_felt(0);
        let c = FixedTrait::from_unscaled_felt(-1);

        assert(!(a < a), 'a < a');
        assert(!(a < b), 'a < b');
        assert(!(a < c), 'a < c');

        assert(b < a, 'b < a');
        assert(!(b < b), 'b < b');
        assert(!(b < c), 'b < c');

        assert(c < a, 'c < a');
        assert(c < b, 'c < b');
        assert(!(c < c), 'c < c');
    }

    #[test]
    fn test_ge() {
        let a = FixedTrait::from_unscaled_felt(1);
        let b = FixedTrait::from_unscaled_felt(0);
        let c = FixedTrait::from_unscaled_felt(-1);

        assert(a >= a, 'a >= a');
        assert(a >= b, 'a >= b');
        assert(a >= c, 'a >= c');

        assert(!(b >= a), 'b >= a');
        assert(b >= b, 'b >= b');
        assert(b >= c, 'b >= c');

        assert(!(c >= a), 'c >= a');
        assert(!(c >= b), 'c >= b');
        assert(c >= c, 'c >= c');
    }

    #[test]
    fn test_gt() {
        let a = FixedTrait::from_unscaled_felt(1);
        let b = FixedTrait::from_unscaled_felt(0);
        let c = FixedTrait::from_unscaled_felt(-1);

        assert(!(a > a), 'a > a');
        assert(a > b, 'a > b');
        assert(a > c, 'a > c');

        assert(!(b > a), 'b > a');
        assert(!(b > b), 'b > b');
        assert(b > c, 'b > c');

        assert(!(c > a), 'c > a');
        assert(!(c > b), 'c > b');
        assert(!(c > c), 'c > c');
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_cos() {
        let a = FixedTrait::new(HALF_PI_u256, false);
        assert(a.cos().try_into().unwrap() == 0, 'invalid half pi');
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_sin() {
        let a = FixedTrait::new(HALF_PI_u256, false);
        assert_precise(a.sin(), ONE, 'invalid half pi', Option::None(()));
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_tan() {
        let a = FixedTrait::new(HALF_PI_u256 / 2, false);
        assert(a.tan().try_into().unwrap() == ONE, 'invalid quarter pi');
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_cosh() {
        let a = FixedTrait::new_unscaled(2, false);
        assert_precise(
            a.cosh(), 69400261068632590000, 'invalid two', Option::None(()),
        ); // 3.762195691016423
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_sinh() {
        let a = FixedTrait::new_unscaled(2, false);
        assert_precise(
            a.sinh(), 66903765734623805000, 'invalid two', Option::None(()),
        ); // 3.6268604077773023
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_tanh() {
        let a = FixedTrait::new_unscaled(2, false);
        assert_precise(
            a.tanh(), 17783170049656136000, 'invalid two', Option::None(()),
        ); // 0.9640275800745076
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_acosh() {
        let a = FixedTrait::new(69400261067392811864, false); // 3.762195691016423
        assert_precise(a.acosh(), 2 * ONE, 'invalid two', Option::None(()));
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_asinh() {
        let a = FixedTrait::new(66903765733337761105, false); // 3.6268604077773023
        assert_precise(a.asinh(), 2 * ONE, 'invalid two', Option::None(()));
    }

    #[test]
    #[available_gas(100000000000)]
    fn test_atanh() {
        let a = FixedTrait::new(16602069666338597000, false); // 0.9
        assert_precise(
            a.atanh(), 27157656144668970000, 'invalid 0.9', Option::None(()),
        ); // 1.4722194895832204
    }
}

