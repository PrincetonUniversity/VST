/* see https://github.com/PrincetonUniversity/VST/issues/868 */

typedef unsigned int u32;
struct my_struct { u32 field1:4; u32 field2:12; u32 field3:16; };

u32 broken_roundtrip_field1(struct my_struct *s) {
    s->field1 = 5000;      /* 4-bit unsigned */
    return s->field1;      /* real behavior: returns 5000 mod 16 = 8*/
}
