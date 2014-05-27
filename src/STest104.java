public class STest104 {
  public static void l() {
    MissileBattery r = new MissileBattery(6);
    MissileBattery q = r;
    r.fire(0);
    q.fire(1);
    r.fire(2);
    q.fire(3);
    r.fire(4);
    q.fire(5);
  }
}
