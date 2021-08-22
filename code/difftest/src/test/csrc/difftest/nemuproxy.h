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

#ifndef __NEMU_PROXY_H
#define __NEMU_PROXY_H

#include <unistd.h>
#include <dlfcn.h>

#include "common.h"

class NemuProxy {
public:
  // public callable functions
  // 内存拷贝
  void (*memcpy)(paddr_t nemu_addr, void *dut_buf, size_t n, bool direction);
  // 寄存器拷贝
  void (*regcpy)(void *dut, bool direction);
  // CSR拷贝
  void (*csrcpy)(void *dut, bool direction);
  // UarchStatus
  void (*uarchstatus_cpy)(void *dut, bool direction);
  
  
  int (*store_commit)(uint64_t *saddr, uint64_t *sdata, uint8_t *smask);
  
  // 执行n条指令
  void (*exec)(uint64_t n);
  
  vaddr_t (*guided_exec)(void *disambiguate_para);
  
  void (*raise_intr)(uint64_t no);
  // 显示寄存器
  void (*isa_reg_display)();

  NemuProxy(int coreid);
private:
};

struct SyncState {
  uint64_t lrscValid;
  uint64_t lrscAddr;
};

struct ExecutionGuide {
  uint64_t exceptionNo;
  uint64_t mtval;   // 微妙
  uint64_t stval;   // 毫秒
};

void ref_misc_put_gmaddr(uint8_t* ptr);

#endif