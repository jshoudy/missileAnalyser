public class UTest102 {
  public static void l() {
    MissileBattery r = new MissileBattery(6);
    MissileBattery q = r;
    r.fire(0);
    q.fire(0);
  }
}
