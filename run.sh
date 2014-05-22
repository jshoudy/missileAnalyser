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


