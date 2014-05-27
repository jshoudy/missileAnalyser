base=$(pwd)
apron=/home/sae/apron
export CLASSPATH=.:$base/soot-2.5.0.jar:$apron/japron/apron.jar:$apron/japron/gmp.jar:$base/bin
export LD_LIBRARY_PATH=$apron/lib

java ch.ethz.sae.Verifier ExampleTest
java ch.ethz.sae.Verifier test_1_SAFE
java ch.ethz.sae.Verifier test_2_UNSAFE
java ch.ethz.sae.Verifier test_3_SAFE
java ch.ethz.sae.Verifier test_4_UNSAFE
java ch.ethz.sae.Verifier test_5_UNSAFE
java ch.ethz.sae.Verifier test_6_SAFE
java ch.ethz.sae.Verifier test_7_UNSAFE
java ch.ethz.sae.Verifier test_8_SAFE
java ch.ethz.sae.Verifier test_10_SAFE
java ch.ethz.sae.Verifier test_11_SAFE
java ch.ethz.sae.Verifier test_12_UNSAFE
java ch.ethz.sae.Verifier test_13_SAFE
java ch.ethz.sae.Verifier test_14_UNSAFE
java ch.ethz.sae.Verifier test_15_SAFE
java ch.ethz.sae.Verifier test_16_SAFE
java ch.ethz.sae.Verifier test_17_SAFE
java ch.ethz.sae.Verifier test_18_SAFE
java ch.ethz.sae.Verifier test_19_UNSAFE
java ch.ethz.sae.Verifier test_20_UNSAFE
#java ch.ethz.sae.Verifier test_21_SAFE
java ch.ethz.sae.Verifier test_22_SAFE
java ch.ethz.sae.Verifier SLoop
java ch.ethz.sae.Verifier SSimpleIf01
java ch.ethz.sae.Verifier SSimpleIf03
java ch.ethz.sae.Verifier SSimpleIf05
java ch.ethz.sae.Verifier STest101
java ch.ethz.sae.Verifier STest104
java ch.ethz.sae.Verifier STest105
java ch.ethz.sae.Verifier STest107
java ch.ethz.sae.Verifier Stest_10_SAFE
java ch.ethz.sae.Verifier Stest_11_SAFE
java ch.ethz.sae.Verifier Stest_13_SAFE
java ch.ethz.sae.Verifier Stest_15_SAFE
java ch.ethz.sae.Verifier Stest_16_SAFE
java ch.ethz.sae.Verifier Stest_17_SAFE
java ch.ethz.sae.Verifier Stest_18_SAFE
java ch.ethz.sae.Verifier Stest_1_SAFE
java ch.ethz.sae.Verifier Stest_21_SAFE
java ch.ethz.sae.Verifier Stest_22_SAFE
java ch.ethz.sae.Verifier Stest_3_SAFE
java ch.ethz.sae.Verifier Stest_6_SAFE
java ch.ethz.sae.Verifier Stest_8_SAFE
java ch.ethz.sae.Verifier UExampleTest
java ch.ethz.sae.Verifier USimpleIf02
java ch.ethz.sae.Verifier USimpleIf04
java ch.ethz.sae.Verifier USimpleIf06
java ch.ethz.sae.Verifier UTest102
java ch.ethz.sae.Verifier UTest103
java ch.ethz.sae.Verifier UTest106
java ch.ethz.sae.Verifier UTest108
java ch.ethz.sae.Verifier Utest_12_UNSAFE
java ch.ethz.sae.Verifier Utest_14_UNSAFE
java ch.ethz.sae.Verifier Utest_19_UNSAFE
java ch.ethz.sae.Verifier Utest_20_UNSAFE
java ch.ethz.sae.Verifier Utest_2_UNSAFE
java ch.ethz.sae.Verifier Utest_4_UNSAFE
java ch.ethz.sae.Verifier Utest_5_UNSAFE
java ch.ethz.sae.Verifier Utest_7_UNSAFE



