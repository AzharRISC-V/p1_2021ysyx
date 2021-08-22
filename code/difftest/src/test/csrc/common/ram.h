/***************************************************************************************
* Copyright (c) 2020-2021 Institute of Computing Technology, Chinese Academy of Sciences
* Copyright (c) 2020-2021 Peng Cheng Laboratory
*
* XiangShan is licensed under Mulan PSL v2.
* You can use this software according to the terms and conditions of the Mulan PSL v2.
* You may obtain a copy of Mulan PSL v2 at:
*          http://license.coscl.org.cn/MulanPSL2
*
* THIS SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, WITHOUT WARRANTIES OF ANY KIND,
* EITHER EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO NON-INFRINGEMENT,
* MERCHANTABILITY OR FIT FOR A PARTICULAR PURPOSE.
*
* See the Mulan PSL v2 for more details.
***************************************************************************************/

#ifndef __RAM_H
#define __RAM_H

#include "common.h"

// #define EMU_RAM_SIZE (256 * 1024 * 1024UL)
#define EMU_RAM_SIZE (8 * 1024 * 1024 * 1024UL)

// 初始化ram：申请空间，并将img文件内容读入这块区域
void init_ram(const char *img);
// 使用完毕清理资源
void ram_finish();

// 返回内存起始位置
void* get_ram_start();
// 返回内存大小
long get_ram_size();

// 返回img数据起始位置，默认加载到内存起始位置
void* get_img_start();
// 返回img数据大小
long get_img_size();

// 内存读取，地址单位是字节
uint64_t pmem_read(uint64_t raddr);
// 内存写入，地址单位是字节
void pmem_write(uint64_t waddr, uint64_t wdata);

#ifdef WITH_DRAMSIM3
#include "axi4.h"

void dramsim3_finish();
void dramsim3_helper_rising(const struct axi_channel &axi);
void dramsim3_helper_falling(struct axi_channel &axi);
#endif

#endif
