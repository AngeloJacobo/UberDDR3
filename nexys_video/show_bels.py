#!/usr/bin/env python3
ddr3_name = 'ddr3_top_inst.ddr3_phy_inst'
def get_cells(name_part):
    return list(map(lambda c: c.second, filter(lambda c: name_part in c.first, ctx.cells)))

def get_cell(name_part):
    return get_cells(name_part)[0]

c1_name = ddr3_name + '.genblk5[0].ISERDESE2_train'
# c2_name = ddr3_name + '.genblk5[1].ISERDESE2_train'
c3_name = ddr3_name + '.genblk5[0].OSERDESE2_train'
# c4_name = ddr3_name + '.genblk5[1].OSERDESE2_train'

c1=get_cell(c1_name)
# c2=get_cell(c2_name)
c3=get_cell(c3_name)
# c4=get_cell(c4_name)

print('show_bels: ' + c1_name + ": ", c1.bel)
# print('show_bels: ' + c2_name + ": ", c2.bel)
print('show_bels: ' + c3_name + ": ", c3.bel)
# print('show_bels: ' + c4_name + ": ", c4.bel)
