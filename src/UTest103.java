public class UTest103 {
  public static void l() {
    MissileBattery r = new MissileBattery(6);
    MissileBattery q = new MissileBattery(2);
    MissileBattery s = r;
    r.fire(0);
    q.fire(1);
    s.fire(0);
  }
}
