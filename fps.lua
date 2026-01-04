local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 63) then
					if (Enum <= 31) then
						if (Enum <= 15) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum > 0) then
											Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										else
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
										end
									elseif (Enum > 2) then
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 5) then
									if (Enum == 4) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									else
										local Edx;
										local Results;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum > 6) then
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										local Results;
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum == 10) then
									Stk[Inst[2]] = not Stk[Inst[3]];
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 13) then
								if (Enum > 12) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum == 14) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum <= 23) then
							if (Enum <= 19) then
								if (Enum <= 17) then
									if (Enum > 16) then
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									else
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum == 18) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 21) then
								if (Enum > 20) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum == 22) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local T;
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 27) then
							if (Enum <= 25) then
								if (Enum > 24) then
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 26) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 29) then
							if (Enum > 28) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 30) then
							do
								return;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 47) then
						if (Enum <= 39) then
							if (Enum <= 35) then
								if (Enum <= 33) then
									if (Enum > 32) then
										Stk[Inst[2]] = Inst[3] ~= 0;
									else
										do
											return Stk[Inst[2]];
										end
									end
								elseif (Enum == 34) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 37) then
								if (Enum == 36) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum == 38) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 43) then
							if (Enum <= 41) then
								if (Enum == 40) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum == 42) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 45) then
							if (Enum > 44) then
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum == 46) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 55) then
						if (Enum <= 51) then
							if (Enum <= 49) then
								if (Enum > 48) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									local Edx;
									local Results;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum > 50) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 53) then
							if (Enum == 52) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 54) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 59) then
						if (Enum <= 57) then
							if (Enum == 56) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 58) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 61) then
						if (Enum > 60) then
							local T;
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum > 62) then
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 95) then
					if (Enum <= 79) then
						if (Enum <= 71) then
							if (Enum <= 67) then
								if (Enum <= 65) then
									if (Enum == 64) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 66) then
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 69) then
								if (Enum > 68) then
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 70) then
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 75) then
							if (Enum <= 73) then
								if (Enum > 72) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local T;
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 74) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 77) then
							if (Enum > 76) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							end
						elseif (Enum > 78) then
							Stk[Inst[2]]();
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						end
					elseif (Enum <= 87) then
						if (Enum <= 83) then
							if (Enum <= 81) then
								if (Enum > 80) then
									Stk[Inst[2]] = {};
								else
									VIP = Inst[3];
								end
							elseif (Enum > 82) then
								local K;
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							end
						elseif (Enum <= 85) then
							if (Enum == 84) then
								local A;
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = not Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum > 86) then
							local A;
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 91) then
						if (Enum <= 89) then
							if (Enum > 88) then
								local T;
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum > 90) then
							if (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						end
					elseif (Enum <= 93) then
						if (Enum == 92) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						else
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum == 94) then
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 111) then
					if (Enum <= 103) then
						if (Enum <= 99) then
							if (Enum <= 97) then
								if (Enum > 96) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum > 98) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 101) then
							if (Enum == 100) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 102) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 107) then
						if (Enum <= 105) then
							if (Enum > 104) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum > 106) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 109) then
						if (Enum == 108) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = not Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum > 110) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 119) then
					if (Enum <= 115) then
						if (Enum <= 113) then
							if (Enum == 112) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum == 114) then
							local T;
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 117) then
						if (Enum > 116) then
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum == 118) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					else
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 123) then
					if (Enum <= 121) then
						if (Enum > 120) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 31) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum > 122) then
						local Results;
						local Edx;
						local Results, Limit;
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					else
						local A;
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 125) then
					if (Enum > 124) then
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum == 126) then
					local B;
					local A;
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Inst[3]));
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					B = Stk[Inst[3]];
					Stk[A + 1] = B;
					Stk[A] = B[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = {};
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Inst[4];
				else
					local K;
					local B;
					local A;
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
					VIP = VIP + 1;
					Inst = Instr[VIP];
					B = Inst[3];
					K = Stk[B];
					for Idx = B + 1, Inst[4] do
						K = K .. Stk[Idx];
					end
					Stk[Inst[2]] = K;
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A](Stk[A + 1]);
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A](Stk[A + 1]);
					VIP = VIP + 1;
					Inst = Instr[VIP];
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!663Q0003043Q007461736B03043Q0077616974026Q00D03F03023Q005F4703053Q00466F72676503043Q00546162732Q033Q0046505303043Q0067616D65030A3Q004765745365727669636503093Q00576F726B737061636503083Q004C69676874696E6703073Q00506C6179657273030A3Q0052756E5365727669636503083Q005261796669656C64030B3Q004C6F63616C506C6179657203053Q007063612Q6C03073Q00456E61626C6564010003093Q00426174636853697A65026Q005940030D3Q00436865636B496E74657276616C026Q003E40030F3Q004D617850656E64696E675175657565030F3Q00436C65616E7570496E74657276616C026Q005E4003123Q004D617850726F63652Q735065724672616D65026Q00344003133Q004175746F52656672657368496E74657276616C025Q0020AC40030C3Q005175616C6974794C6576656C03073Q004C6576656C3031030D3Q0044697361626C65506F737446582Q01030E3Q0044697361626C65536861646F777303063Q00466F67456E64023Q00C088C30042030A3Q004272696768746E652Q73026Q00F03F030F3Q0054652Q7261696E53696D706C696679030A3Q004D7574654E6F74696679030E3Q004D61696E436F2Q6E656374696F6E00030A3Q004C2Q6F70546872656164030D3Q00436C65616E7570546872656164030D3Q0052656672657368546872656164030C3Q0050656E64696E675175657565030C3Q00497350726F63652Q73696E6703133Q00497350656E64696E6750726F63652Q73696E67030B3Q004973526573652Q74696E67030B3Q004C617374436C65616E7570028Q00030B3Q004C61737452656672657368030D3Q0043726561746553656374696F6E031B3Q0046505320422Q6F737465722028457874656E646564204D6F646529030C3Q00437265617465546F2Q676C6503043Q004E616D6503123Q00456E61626C652046505320422Q6F73746572030C3Q0043752Q72656E7456616C756503043Q00466C616703103Q00465053422Q6F73746572546F2Q676C6503083Q0043612Q6C6261636B030D3Q004E6F74696669636174696F6E73030D3Q004650534D7574654E6F74696679030C3Q00437265617465536C69646572030A3Q0042617463682053697A6503053Q0052616E6765026Q004940025Q00C0724003093Q00496E6372656D656E74026Q003940030C3Q00465053426174636853697A6503123Q00436865636B20496E74657276616C20287329026Q002440026Q004E40026Q00144003103Q00465053436865636B496E74657276616C03143Q00436C65616E757020496E74657276616C20287329025Q00C0824003123Q00465053436C65616E7570496E74657276616C030D3Q004D617820506572204672616D65030E3Q004650534D61785065724672616D6503143Q004175746F205265667265736820286D656E697429026Q002E40030E3Q004650534175746F5265667265736803143Q0044697361626C6520506F737420452Q666563747303103Q0046505344697361626C65506F73744658030F3Q0044697361626C6520536861646F777303113Q0046505344697361626C65536861646F7773030C3Q0043726561746542752Q746F6E03113Q00466F72636520436C65616E7570204E6F77030E3Q0052756E2046752Q6C2053772Q657003053Q00465053554903063Q00546F2Q676C6503053Q00526573657403083Q005265736574465053030E3Q0044656661756C7420456E61626C6503053Q007461626C6503063Q00696E7365727403073Q00436C65616E7570030D3Q00556E6C6F6164436C65616E757003053Q007072696E7403303Q005B4650535D204C6F61646564202D20457874656E646564204D6F646520283247422052414D204F7074696D697A656429006A012Q00121A3Q00013Q0020355Q000200122Q000100038Q0002000100124Q00043Q00206Q000500066Q00013Q0004505Q000100121A3Q00043Q0020235Q00050020235Q00060006075Q00013Q0004505Q000100121A3Q00043Q0020235Q00050020235Q00060020235Q00070006075Q00013Q0004505Q000100121A3Q00083Q00207D5Q000900122Q0002000A8Q0002000200122Q000100083Q00202Q00010001000900122Q0003000B6Q00010003000200122Q000200083Q00202Q00020002000900122Q0004000C4Q001C000200040002001211000300083Q00202Q00030003000900122Q0005000D6Q00030005000200122Q000400043Q00202Q00040004000500202Q00050004000600202Q00050005000700202Q00060004000E00202Q00070002000F00121A000800103Q00067800093Q000100022Q001F3Q00024Q001F3Q00074Q00420008000200014Q00083Q000E00302Q00080011001200302Q00080013001400302Q00080015001600302Q00080017001400302Q00080018001900302Q0008001A001B00302Q0008001C001D00302Q0008001E001F00306F00080020002100302Q00080022002100302Q00080023002400302Q00080025002600302Q00080027002100302Q0008002800124Q000900016Q000A3Q000A00302Q000A0029002A00302Q000A002B002A00302Q000A002C002A00306F000A002D002A2Q0068000B5Q00102Q000A002E000B00302Q000A002F001200302Q000A0030001200302Q000A0031001200302Q000A0032003300302Q000A00340033000226000B00013Q000226000C00023Q000226000D00033Q000678000E0004000100032Q001F3Q000A4Q001F3Q00084Q001F3Q000B3Q000226000F00053Q000226001000063Q00067800110007000100022Q001F8Q001F3Q000F3Q00067800120008000100032Q001F3Q00084Q001F3Q00064Q001F3Q000C3Q00067800130009000100022Q001F3Q00104Q001F3Q00073Q0002260014000A3Q0006780015000B000100042Q001F3Q00084Q001F3Q00014Q001F8Q001F3Q000D3Q0006780016000C000100082Q001F3Q000A4Q001F3Q00154Q001F3Q00114Q001F3Q00024Q001F3Q00084Q001F3Q00144Q001F3Q00034Q001F7Q0006780017000D000100072Q001F3Q000A4Q001F3Q00084Q001F3Q00144Q001F3Q00104Q001F3Q00074Q001F3Q00134Q001F3Q00033Q0006780018000E000100032Q001F3Q00084Q001F3Q000A4Q001F3Q00173Q0006780019000F000100062Q001F3Q000A4Q001F3Q00084Q001F3Q00024Q001F3Q00104Q001F3Q00074Q001F3Q00133Q000678001A0010000100012Q001F3Q000A3Q000678001B0011000100032Q001F3Q000A4Q001F3Q00084Q001F3Q000B3Q000678001C0012000100012Q001F3Q000A3Q000678001D0013000100072Q001F3Q000A4Q001F3Q00084Q001F3Q000B4Q001F3Q000E4Q001F3Q00154Q001F3Q00164Q001F3Q00123Q000678001E0014000100012Q001F3Q000A3Q000678001F00150001000C2Q001F3Q00084Q001F3Q000B4Q001F3Q000A4Q001F3Q00154Q001F3Q00164Q001F3Q000C4Q001F8Q001F3Q00184Q001F3Q00194Q001F3Q001B4Q001F3Q001D4Q001F3Q00123Q00067800200016000100072Q001F3Q00084Q001F3Q001A4Q001F3Q001C4Q001F3Q001E4Q001F3Q000A4Q001F3Q000B4Q001F3Q00123Q00205F00210005003500122Q002300366Q00210023000100202Q0021000500374Q00233Q000400302Q00230038003900102Q0023003A000900302Q0023003B003C00067800240017000100042Q001F3Q000C4Q001F3Q000A4Q001F3Q001F4Q001F3Q00203Q0010550023003D00244Q00210023000200202Q0022000500374Q00243Q000400302Q00240038003E00202Q0025000800284Q002500253Q00102Q0024003A002500302Q0024003B003F00067800250018000100022Q001F3Q000C4Q001F3Q00083Q00107E0024003D00254Q00220024000100202Q0022000500404Q00243Q000600302Q0024003800412Q0051002500023Q001208002600433Q001208002700444Q005E00250002000100104300240042002500306F0024004500460020230025000800130010430024003A002500306F0024003B004700067800250019000100022Q001F3Q000C4Q001F3Q00083Q00107E0024003D00254Q00220024000100202Q0022000500404Q00243Q000600302Q0024003800482Q0051002500023Q001208002600493Q0012080027004A4Q005E00250002000100104300240042002500306F00240045004B0020230025000800150010430024003A002500306F0024003B004C0006780025001A000100022Q001F3Q000C4Q001F3Q00083Q00107E0024003D00254Q00220024000100202Q0022000500404Q00243Q000600302Q00240038004D2Q0051002500023Q0012080026004A3Q0012080027004E4Q005E00250002000100104300240042002500306F0024004500160020230025000800180010430024003A002500306F0024003B004F0006780025001B000100022Q001F3Q000C4Q001F3Q00083Q00107E0024003D00254Q00220024000100202Q0022000500404Q00243Q000600302Q0024003800502Q0051002500023Q001208002600493Q001208002700434Q005E00250002000100104300240042002500306F00240045004B00202300250008001A0010430024003A002500306F0024003B00510006780025001C000100022Q001F3Q000C4Q001F3Q00083Q00107E0024003D00254Q00220024000100202Q0022000500404Q00243Q000600302Q0024003800522Q0051002500023Q001208002600163Q001208002700194Q005E00250002000100104300240042002500301400240045005300202Q00250008001C00202Q00250025004A00102Q0024003A002500302Q0024003B00540006780025001D000100022Q001F3Q000C4Q001F3Q00083Q00107E0024003D00254Q00220024000100202Q0022000500374Q00243Q000400302Q0024003800550020230025000800200010430024003A002500306F0024003B00560006780025001E000100032Q001F3Q000C4Q001F3Q00084Q001F3Q00153Q00107E0024003D00254Q00220024000100202Q0022000500374Q00243Q000400302Q0024003800570020230025000800220010430024003A002500306F0024003B00580006780025001F000100032Q001F3Q000C4Q001F3Q00084Q001F3Q00153Q00107E0024003D00254Q00220024000100202Q0022000500594Q00243Q000200302Q00240038005A00067800250020000100042Q001F3Q000C4Q001F3Q000B4Q001F3Q000A4Q001F3Q00123Q00107E0024003D00254Q00220024000100202Q0022000500594Q00243Q000200302Q00240038005B00067800250021000100042Q001F3Q000C4Q001F3Q000A4Q001F3Q00124Q001F3Q00163Q00102D0024003D00254Q00220024000100122Q002200043Q00202Q0022002200054Q00233Q000200102Q0023005D002100067800240022000100052Q001F3Q000A4Q001F3Q00094Q001F3Q001F4Q001F3Q00204Q001F3Q00213Q0010430023005E00240010430022005C002300121A002200043Q002023002200220005000226002300233Q0010130022005F00234Q0022000C3Q00122Q002300606Q0024001F6Q00220024000100122Q002200613Q00202Q00220022006200202Q0023000400634Q002400206Q002200240001002023002200040064000662002200602Q0100010004503Q00602Q012Q005100225Q001043000400640022001202002200613Q00202Q00220022006200202Q0023000400644Q002400206Q00220024000100122Q002200653Q00122Q002300666Q0022000200016Q00013Q00243Q00033Q0003183Q0047657450726F70657274794368616E6765645369676E616C030B3Q004C6F63616C506C6179657203073Q00436F2Q6E656374000A4Q004B7Q00206Q000100122Q000200028Q0002000200206Q000300067800023Q000100022Q006A3Q00014Q006A8Q00653Q000200012Q001E3Q00013Q00013Q00013Q00030B3Q004C6F63616C506C6179657200044Q006A3Q00013Q0020235Q00012Q00768Q001E3Q00017Q00043Q0003053Q007461626C6503053Q00636C65617203053Q0070616972730001113Q00121A000100013Q0020230001000100020006070001000900013Q0004503Q0009000100121A000100013Q0020230001000100022Q001F00026Q00240001000200012Q001E3Q00013Q00121A000100034Q001F00026Q00700001000200030004503Q000E000100206B3Q0004000400065A0001000D000100010004503Q000D00012Q001E3Q00017Q00053Q0003053Q007063612Q6C03043Q007761726E03063Q005B4650535D2003083Q0020652Q726F723A2003083Q00746F737472696E6702103Q00121A000200014Q001F000300014Q00700002000200030006620002000E000100010004503Q000E000100121A000400023Q001275000500036Q00065Q00122Q000700043Q00122Q000800056Q000900036Q0008000200024Q0005000500084Q0004000200012Q0020000200024Q001E3Q00017Q00063Q0003063Q00747970656F6603083Q00456E756D4974656D03043Q007479706503063Q00737472696E6703043Q00456E756D030C3Q005175616C6974794C6576656C01123Q00121A000100014Q001F00026Q000E00010002000200260600010006000100020004503Q000600012Q00203Q00023Q00121A000100034Q001F00026Q000E0001000200020026060001000F000100040004503Q000F000100121A000100053Q0020230001000100062Q0003000100014Q0020000100024Q000F000100014Q0020000100024Q001E3Q00017Q000C3Q0003023Q006F7303053Q00636C6F636B030C3Q00497350726F63652Q73696E6703133Q00497350656E64696E6750726F63652Q73696E6703073Q00456E61626C656403043Q007461736B03043Q0077616974029A5Q99B93F0100030C3Q0050656E64696E67517565756503043Q007761726E032B3Q005B4650535D20466F72636520726573657420737475636B20666C6167732061667465722074696D656F757401343Q00121A000100013Q0020230001000100022Q003A0001000100022Q006A00025Q0020230002000200030006620002000B000100010004503Q000B00012Q006A00025Q0020230002000200040006070002001B00013Q0004503Q001B000100121A000200013Q0020230002000200022Q003A0002000100022Q00520002000200010006410002001B00013Q0004503Q001B00012Q006A000200013Q00202300020002000500066200020016000100010004503Q001600010004503Q001B000100121A000200063Q002023000200020007001208000300084Q00240002000200010004503Q000300012Q006A00025Q00202300020002000300066200020023000100010004503Q002300012Q006A00025Q0020230002000200042Q000A000200023Q0004503Q002500012Q004C00026Q0021000200013Q00066200020032000100010004503Q003200012Q006A00035Q0030190003000300094Q00035Q00302Q0003000400094Q000300026Q00045Q00202Q00040004000A4Q00030002000100122Q0003000B3Q00122Q0004000C6Q0003000200012Q0020000200024Q001E3Q00017Q00093Q0003023Q005F4703053Q00466F726765030C3Q004D696E696E67436F6E666967030A3Q004175746F4D696E696E67030A3Q004661726D436F6E66696703083Q004175746F4661726D03113Q004D696E696E674D61676963436172706574030F3Q004661726D4D61676963436172706574030B3Q004D6167696343617270657401273Q00121A000100013Q00202300010001000200066200010006000100010004503Q000600012Q002100026Q0020000200023Q0020230002000100030006070002000B00013Q0004503Q000B00010020230002000100030020230002000200040020230003000100050006070003001000013Q0004503Q001000010020230003000100050020230003000300060026063Q0016000100070004503Q001600010006070002001600013Q0004503Q001600012Q0021000400014Q0020000400023Q0026063Q001C000100080004503Q001C00010006070003001C00013Q0004503Q001C00012Q0021000400014Q0020000400023Q0026063Q0024000100090004503Q0024000100066200020022000100010004503Q002200010006070003002400013Q0004503Q002400012Q0021000400014Q0020000400024Q002100046Q0020000400024Q001E3Q00017Q00043Q0003023Q005F4703053Q00466F726765030C3Q004D696E696E67436F6E666967030A3Q004175746F4D696E696E67000B3Q00121A3Q00013Q0020235Q00020006250001000900013Q0004503Q0009000100202300013Q00030006070001000900013Q0004503Q0009000100202300013Q00030020230001000100042Q0020000100024Q001E3Q00017Q000A3Q0003063Q00697061697273030B3Q004765744368696C6472656E03043Q004E616D65030B3Q004D61676963436172706574030F3Q004661726D4D6167696343617270657403093Q00466C79436172706574030E3Q0054656C65706F727443617270657403113Q004D696E696E674D6167696343617270657403053Q007063612Q6C03073Q0044657374726F79001D3Q0012383Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q001A000100202300050004000300265B00050011000100040004503Q0011000100265B00050011000100050004503Q0011000100265B00050011000100060004503Q0011000100265B00050011000100070004503Q001100010026060005001A000100080004503Q001A00012Q006A000600014Q001F000700054Q000E0006000200020006620006001A000100010004503Q001A000100121A000600093Q00202300070004000A2Q001F000800044Q006500060008000100065A3Q0006000100020004503Q000600012Q001E3Q00017Q00063Q00030A3Q004D7574654E6F7469667903063Q004E6F7469667903043Q007761726E03063Q005B4650535D2003083Q00746F737472696E6703023Q003A2003214Q006A00035Q0020230003000300010006070003000500013Q0004503Q000500012Q001E3Q00014Q006A000300013Q0006070003000C00013Q0004503Q000C00012Q006A000300013Q00202300030003000200066200030018000100010004503Q0018000100121A000300033Q00122A000400043Q00122Q000500056Q00068Q00050002000200122Q000600063Q00122Q000700056Q000800016Q0007000200024Q0004000400074Q0003000200016Q00014Q006A000300023Q001208000400023Q00067800053Q000100042Q006A3Q00014Q001F8Q001F3Q00014Q001F3Q00024Q00650003000500012Q001E3Q00013Q00013Q00053Q0003063Q004E6F7469667903053Q005469746C6503073Q00436F6E74656E7403083Q004475726174696F6E026Q000840000E4Q002E7Q00206Q00014Q00023Q00034Q000300013Q00102Q0002000200034Q000300023Q00102Q0002000300034Q000300033Q00062Q0003000B000100010004503Q000B0001001208000300053Q0010430002000400032Q00653Q000200012Q001E3Q00017Q00033Q0003093Q0043686172616374657203063Q00506172656E7403053Q007063612Q6C01174Q006A00016Q003A0001000100020006070001000C00013Q0004503Q000C00012Q006A000100013Q0006070001000C00013Q0004503Q000C00012Q006A000100013Q0020230001000100010006693Q000C000100010004503Q000C00012Q001E3Q00013Q0006073Q001100013Q0004503Q0011000100202300013Q000200066200010012000100010004503Q001200012Q001E3Q00013Q00121A000100033Q00067800023Q000100012Q001F8Q00240001000200012Q001E3Q00013Q00013Q000C3Q00030E3Q0046696E6446697273744368696C6403073Q00416E696D6174652Q033Q00497341030B3Q004C6F63616C53637269707403083Q0044697361626C65642Q0103153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403083Q00416E696D61746F7203063Q0069706169727303193Q00476574506C6179696E67416E696D6174696F6E547261636B7303043Q0053746F7000214Q002F7Q00206Q000100122Q000200028Q0002000200064Q000C00013Q0004503Q000C000100207100013Q0003001208000300044Q001C0001000300020006070001000C00013Q0004503Q000C000100306F3Q000500062Q006A00015Q002071000100010007001208000300084Q001C0001000300020006070001002000013Q0004503Q00200001002071000200010007001208000400094Q001C0002000400020006070002002000013Q0004503Q0020000100121A0003000A3Q00207100040002000B2Q0049000400054Q004400033Q00050004503Q001E000100207100080007000C2Q002400080002000100065A0003001C000100020004503Q001C00012Q001E3Q00017Q00023Q0003063Q00506172656E7403053Q007063612Q6C010B3Q0006073Q000500013Q0004503Q0005000100202300013Q000100066200010006000100010004503Q000600012Q001E3Q00013Q00121A000100023Q00067800023Q000100012Q001F8Q00240001000200012Q001E3Q00013Q00013Q00173Q002Q033Q0049734103083Q00426173655061727403083Q004D6174657269616C03043Q00456E756D030D3Q00536D2Q6F7468506C6173746963030B3Q005265666C656374616E6365028Q00030A3Q0043617374536861646F77010003083Q004D6573685061727403093Q00546578747572654944034Q0003053Q00446563616C03073Q0054657874757265030C3Q005472616E73706172656E6379026Q00F03F030F3Q005061727469636C65456D692Q74657203053Q00547261696C03053Q00536D6F6B6503043Q004669726503083Q00537061726B6C657303043Q004265616D03073Q00456E61626C6564004E4Q002F7Q00206Q000100122Q000200028Q0002000200064Q001800013Q0004503Q001800012Q006A7Q00125D000100043Q00202Q00010001000300202Q00010001000500104Q000300019Q0000304Q000600079Q0000304Q000800099Q0000206Q000100122Q0002000A8Q0002000200064Q004D00013Q0004503Q004D00012Q006A7Q00306F3Q000B000C0004503Q004D00012Q006A7Q0020715Q00010012080002000D4Q001C3Q000200020006623Q0024000100010004503Q002400012Q006A7Q0020715Q00010012080002000E4Q001C3Q000200020006073Q002700013Q0004503Q002700012Q006A7Q00306F3Q000F00100004503Q004D00012Q006A7Q0020715Q0001001208000200114Q001C3Q000200020006623Q004B000100010004503Q004B00012Q006A7Q0020715Q0001001208000200124Q001C3Q000200020006623Q004B000100010004503Q004B00012Q006A7Q0020715Q0001001208000200134Q001C3Q000200020006623Q004B000100010004503Q004B00012Q006A7Q0020715Q0001001208000200144Q001C3Q000200020006623Q004B000100010004503Q004B00012Q006A7Q0020715Q0001001208000200154Q001C3Q000200020006623Q004B000100010004503Q004B00012Q006A7Q0020715Q0001001208000200164Q001C3Q000200020006073Q004D00013Q0004503Q004D00012Q006A7Q00306F3Q001700092Q001E3Q00017Q00013Q0003053Q007063612Q6C00083Q00121A3Q00013Q00067800013Q000100042Q006A8Q006A3Q00014Q006A3Q00024Q006A3Q00034Q00243Q000200012Q001E3Q00013Q00013Q00163Q00030E3Q0044697361626C65536861646F7773030D3Q00476C6F62616C536861646F7773010003063Q00466F67456E64030A3Q004272696768746E652Q73030D3Q0044697361626C65506F7374465803063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030A3Q00506F7374452Q6665637403073Q00456E61626C6564030F3Q0054652Q7261696E53696D706C69667903153Q0046696E6446697273744368696C644F66436C612Q7303073Q0054652Q7261696E030D3Q0057617465725761766553697A65028Q00030E3Q0057617465725761766553702Q656403103Q0057617465725265666C656374616E636503113Q0057617465725472616E73706172656E6379030C3Q005175616C6974794C6576656C03083Q0073652Q74696E677303093Q0052656E646572696E6700414Q006A7Q0020235Q00010006073Q000600013Q0004503Q000600012Q006A3Q00013Q00306F3Q000200032Q006A3Q00014Q006400015Q00202Q00010001000400104Q000400016Q00016Q00015Q00202Q00010001000500104Q000500019Q0000206Q000600064Q002000013Q0004503Q0020000100121A3Q00074Q007B000100013Q00202Q0001000100084Q000100029Q00000200044Q001E00010020710005000400090012080007000A4Q001C0005000700020006070005001E00013Q0004503Q001E000100306F0004000B000300065A3Q0018000100020004503Q001800012Q006A7Q0020235Q000C0006073Q002E00013Q0004503Q002E00012Q006A3Q00023Q0020715Q000D0012080002000E4Q001C3Q000200020006073Q002E00013Q0004503Q002E000100306F3Q000F001000306F3Q0011001000306F3Q0012001000306F3Q001300102Q006A3Q00034Q006A00015Q0020230001000100142Q000E3Q000200020006073Q004000013Q0004503Q0040000100121A000100153Q0006070001004000013Q0004503Q0040000100121A000100154Q003A0001000100020020230001000100160006070001004000013Q0004503Q0040000100121A000100154Q003A000100010002002023000100010016001043000100144Q001E3Q00017Q00043Q00030C3Q00497350726F63652Q73696E672Q0103043Q007461736B03053Q00737061776E00144Q006A7Q0020235Q00010006073Q000500013Q0004503Q000500012Q001E3Q00014Q006A7Q00306F3Q0001000200121A3Q00033Q0020235Q000400067800013Q000100082Q006A3Q00014Q006A3Q00024Q006A3Q00034Q006A3Q00044Q006A3Q00054Q006A3Q00064Q006A3Q00074Q006A8Q00243Q000200012Q001E3Q00013Q00013Q00063Q0003053Q007063612Q6C03043Q007761726E03173Q005B4650535D2066752Q6C53772Q657020652Q726F723A2003083Q00746F737472696E67030C3Q00497350726F63652Q73696E67012Q00163Q00121A3Q00013Q00067800013Q000100072Q006A8Q006A3Q00014Q006A3Q00024Q006A3Q00034Q006A3Q00044Q006A3Q00054Q006A3Q00064Q00703Q000200010006623Q0013000100010004503Q0013000100121A000200023Q001260000300033Q00122Q000400046Q000500016Q0004000200024Q0003000300044Q0002000200012Q006A000200073Q00306F0002000500062Q001E3Q00013Q00013Q000D3Q0003063Q00697061697273030A3Q00476574506C617965727303093Q004368617261637465722Q01028Q00030B3Q004765744368696C6472656E03073Q00456E61626C656403063Q00506172656E7403093Q00426174636853697A6503043Q007461736B03043Q0077616974029A5Q99A93F027B14AE47E17A843F00444Q00099Q003Q000100016Q00018Q000100019Q0000122Q000100016Q000200023Q00202Q0002000200024Q000200036Q00013Q000300044Q001000010020230006000500030006070006001000013Q0004503Q0010000100202300060005000300206B3Q0006000400065A0001000B000100020004503Q000B0001001208000100053Q001208000200053Q00067800033Q000100072Q006A3Q00034Q006A3Q00044Q001F3Q00014Q001F3Q00024Q006A3Q00054Q001F8Q001F3Q00034Q0005000400063Q00202Q0004000400064Q00040002000200122Q000500016Q000600046Q00050002000700044Q004000012Q006A000A00033Q002023000A000A0007000662000A0028000100010004503Q002800010004503Q004200010006070009003C00013Q0004503Q003C0001002023000A00090008000607000A003C00013Q0004503Q003C00012Q0003000A3Q0009000662000A003C000100010004503Q003C00012Q001F000A00034Q0067000B00096Q000A000200014Q000A00033Q00202Q000A000A00094Q000A0002000A00262Q000A003C000100050004503Q003C000100121A000A000A3Q002023000A000A000B001208000B000C4Q0024000A0002000100121A000A000A3Q002023000A000A000B001208000B000D4Q0024000A0002000100065A00050023000100020004503Q002300012Q000F000400044Q001E3Q00013Q00013Q00083Q0003073Q00456E61626C6564026Q00F03F03123Q004D617850726F63652Q735065724672616D65028Q0003093Q0048656172746265617403043Q0057616974030B3Q004765744368696C6472656E03063Q00697061697273012F4Q006A00015Q00202300010001000100066200010005000100010004503Q000500012Q001E3Q00014Q006A000100014Q001B00028Q0001000200014Q000100023Q00202Q0001000100024Q000100026Q000100033Q00202Q0001000100024Q000100036Q000100026Q00025Q00202Q00020002000300062Q00020019000100010004503Q00190001001208000100044Q0046000100026Q000100043Q00202Q00010001000500202Q0001000100064Q00010002000100207100013Q00072Q003000010002000200122Q000200086Q000300016Q00020002000400044Q002B00012Q006A00075Q00202300070007000100066200070024000100010004503Q002400010004503Q002D00012Q006A000700054Q00030007000700060006620007002B000100010004503Q002B00012Q006A000700064Q001F000800064Q002400070002000100065A0002001F000100020004503Q001F00012Q000F000100014Q001E3Q00017Q00063Q0003133Q00497350656E64696E6750726F63652Q73696E67030C3Q0050656E64696E675175657565028Q002Q0103043Q007461736B03053Q00737061776E00184Q006A7Q0020235Q00010006623Q0009000100010004503Q000900012Q006A7Q0020235Q00022Q003C7Q0026063Q000A000100030004503Q000A00012Q001E3Q00014Q006A7Q00306F3Q0001000400121A3Q00053Q0020235Q000600067800013Q000100072Q006A8Q006A3Q00014Q006A3Q00024Q006A3Q00034Q006A3Q00044Q006A3Q00054Q006A3Q00064Q00243Q000200012Q001E3Q00013Q00013Q00063Q0003053Q007063612Q6C03043Q007761726E031C3Q005B4650535D2070726F63652Q7350656E64696E6720652Q726F723A2003083Q00746F737472696E6703133Q00497350656E64696E6750726F63652Q73696E67012Q00163Q00121A3Q00013Q00067800013Q000100072Q006A8Q006A3Q00014Q006A3Q00024Q006A3Q00034Q006A3Q00044Q006A3Q00054Q006A3Q00064Q00703Q000200010006623Q0013000100010004503Q0013000100121A000200023Q001260000300033Q00122Q000400046Q000500016Q0004000200024Q0003000300044Q0002000200012Q006A00025Q00306F0002000500062Q001E3Q00013Q00013Q00103Q00028Q00030C3Q0050656E64696E67517565756503073Q00456E61626C656403133Q00497350656E64696E6750726F63652Q73696E6703053Q007461626C6503063Q0072656D6F7665026Q00F03F03063Q00506172656E742Q033Q0049734103053Q004D6F64656C03153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403093Q0043686172616374657203123Q004D617850726F63652Q735065724672616D6503093Q0048656172746265617403043Q005761697400403Q0012083Q00014Q006A00015Q0020230001000100022Q003C000100013Q000E390001003F000100010004503Q003F00012Q006A000100013Q0020230001000100030006070001003F00013Q0004503Q003F00012Q006A00015Q0020230001000100040006070001003F00013Q0004503Q003F000100121A000100053Q00206E0001000100064Q00025Q00202Q00020002000200122Q000300076Q00010003000200062Q0001003400013Q0004503Q003400010020230002000100080006070002003400013Q0004503Q003400012Q006A000200024Q0015000300016Q00020002000100202Q00020001000900122Q0004000A6Q00020004000200062Q0002003400013Q0004503Q0034000100207100020001000B0012080004000C4Q001C0002000400020006070002003400013Q0004503Q003400012Q006A000200034Q003A0002000100020006070002003100013Q0004503Q003100012Q006A000200043Q0006070002003100013Q0004503Q003100012Q006A000200043Q00202300020002000D00067C00010034000100020004503Q003400012Q006A000200054Q001F000300014Q00240002000200010020315Q00072Q006A000200013Q00202300020002000E00063B0002000100013Q0004503Q000100010012083Q00014Q0032000200063Q00202Q00020002000F00202Q0002000200104Q00020002000100044Q000100012Q001E3Q00017Q00053Q0003073Q00456E61626C656403053Q007063612Q6C03043Q007761726E031D3Q005B4650535D2044657363656E64616E74412Q64656420652Q726F723A2003083Q00746F737472696E6701164Q006A00015Q00202300010001000100066200010005000100010004503Q000500012Q001E3Q00013Q00121A000100023Q00067800023Q000100042Q006A3Q00014Q006A8Q001F8Q006A3Q00024Q007000010002000200066200010015000100010004503Q0015000100121A000300033Q001260000400043Q00122Q000500056Q000600026Q0005000200024Q0004000400054Q0003000200012Q001E3Q00013Q00013Q00043Q00030C3Q0050656E64696E675175657565030F3Q004D617850656E64696E67517565756503053Q007461626C6503063Q00696E7365727400114Q004D7Q00206Q00019Q004Q000100013Q00202Q00010001000200062Q0001000800013Q0004503Q000800012Q001E3Q00013Q00121A3Q00033Q0020125Q00044Q00015Q00202Q0001000100014Q000200028Q000200016Q00038Q000100016Q00017Q00033Q00030A3Q004C2Q6F7054687265616403043Q007461736B03053Q00737061776E00124Q006A7Q0020235Q00010006073Q000500013Q0004503Q000500012Q001E3Q00014Q006A7Q00121A000100023Q00202300010001000300067800023Q000100062Q006A3Q00014Q006A3Q00024Q006A3Q00034Q006A3Q00044Q006A3Q00054Q006A8Q000E0001000200020010433Q000100012Q001E3Q00013Q00013Q000A3Q0003073Q00456E61626C656403053Q007063612Q6C03043Q007761726E03123Q005B4650535D206C2Q6F7020652Q726F723A2003083Q00746F737472696E6703043Q007461736B03043Q0077616974026Q00F03F030A3Q004C2Q6F705468726561642Q001D4Q006A7Q0020235Q00010006073Q001A00013Q0004503Q001A000100121A3Q00023Q00067800013Q000100052Q006A8Q006A3Q00014Q006A3Q00024Q006A3Q00034Q006A3Q00044Q00703Q000200010006625Q000100010004505Q000100121A000200033Q001260000300043Q00122Q000400056Q000500016Q0004000200024Q0003000300044Q000200020001001229000200063Q00202Q00020002000700122Q000300086Q00020002000100046Q00012Q006A3Q00053Q00306F3Q0009000A2Q001E3Q00013Q00013Q00073Q0003043Q007461736B03043Q0077616974030D3Q00436865636B496E74657276616C03073Q00456E61626C656403063Q00697061697273030A3Q00476574506C617965727303093Q00436861726163746572002A3Q0012183Q00013Q00206Q00024Q00015Q00202Q0001000100036Q000200019Q0000206Q000400064Q000A000100010004503Q000A00012Q001E3Q00013Q00121A3Q00054Q007B000100013Q00202Q0001000100064Q000100029Q00000200044Q002700010020230005000400070006070005002400013Q0004503Q002400012Q006A000500024Q003A0005000100020006070005001F00013Q0004503Q001F00012Q006A000500033Q0006070005001F00013Q0004503Q001F00012Q006A000500033Q00067C0004001E000100050004503Q001E00012Q004C00056Q0021000500013Q00066200050024000100010004503Q002400012Q006A000600043Q0020230007000400072Q002400060002000100121A000500013Q0020230005000500022Q004F00050001000100065A3Q0010000100020004503Q001000012Q001E3Q00017Q00053Q00030A3Q004C2Q6F7054687265616403053Q007063612Q6C03043Q007461736B03063Q0063616E63656C2Q000D4Q006A7Q0020235Q00010006073Q000C00013Q0004503Q000C000100121A3Q00023Q001240000100033Q00202Q0001000100044Q00025Q00202Q0002000200016Q000200019Q0000304Q000100052Q001E3Q00017Q00033Q00030D3Q00436C65616E757054687265616403043Q007461736B03053Q00737061776E000F4Q006A7Q0020235Q00010006073Q000500013Q0004503Q000500012Q001E3Q00014Q006A7Q00121A000100023Q00202300010001000300067800023Q000100032Q006A3Q00014Q006A3Q00024Q006A8Q000E0001000200020010433Q000100012Q001E3Q00013Q00013Q000A3Q0003073Q00456E61626C656403053Q007063612Q6C03043Q007761726E031A3Q005B4650535D20636C65616E7570206C2Q6F7020652Q726F723A2003083Q00746F737472696E6703043Q007461736B03043Q0077616974026Q00F03F030D3Q00436C65616E75705468726561642Q001B4Q006A7Q0020235Q00010006073Q001800013Q0004503Q0018000100121A3Q00023Q00067800013Q000100032Q006A8Q006A3Q00014Q006A3Q00024Q00703Q000200010006625Q000100010004505Q000100121A000200033Q001260000300043Q00122Q000400056Q000500016Q0004000200024Q0003000300044Q000200020001001229000200063Q00202Q00020002000700122Q000300086Q00020002000100046Q00012Q006A3Q00023Q00306F3Q0009000A2Q001E3Q00013Q00013Q00083Q0003043Q007461736B03043Q0077616974030F3Q00436C65616E7570496E74657276616C03073Q00456E61626C6564030C3Q0050656E64696E675175657565030B3Q004C617374436C65616E757003023Q006F7303053Q00636C6F636B00143Q0012183Q00013Q00206Q00024Q00015Q00202Q0001000100036Q000200019Q0000206Q000400064Q000A000100010004503Q000A00012Q001E3Q00014Q006A3Q00014Q000C000100023Q00202Q0001000100056Q000200016Q00023Q00122Q000100073Q00202Q0001000100084Q00010001000200104Q000600016Q00017Q00053Q00030D3Q00436C65616E757054687265616403053Q007063612Q6C03043Q007461736B03063Q0063616E63656C2Q000D4Q006A7Q0020235Q00010006073Q000C00013Q0004503Q000C000100121A3Q00023Q001240000100033Q00202Q0001000100044Q00025Q00202Q0002000200016Q000200019Q0000304Q000100052Q001E3Q00017Q00033Q00030D3Q005265667265736854687265616403043Q007461736B03053Q00737061776E00134Q006A7Q0020235Q00010006073Q000500013Q0004503Q000500012Q001E3Q00014Q006A7Q00121A000100023Q00202300010001000300067800023Q000100072Q006A3Q00014Q006A3Q00024Q006A8Q006A3Q00034Q006A3Q00044Q006A3Q00054Q006A3Q00064Q000E0001000200020010433Q000100012Q001E3Q00013Q00013Q000A3Q0003073Q00456E61626C656403053Q007063612Q6C03043Q007761726E031A3Q005B4650535D2072656672657368206C2Q6F7020652Q726F723A2003083Q00746F737472696E6703043Q007461736B03043Q0077616974026Q00F03F030D3Q00526566726573685468726561642Q001F4Q006A7Q0020235Q00010006073Q001C00013Q0004503Q001C000100121A3Q00023Q00067800013Q000100072Q006A8Q006A3Q00014Q006A3Q00024Q006A3Q00034Q006A3Q00044Q006A3Q00054Q006A3Q00064Q00703Q000200010006625Q000100010004505Q000100121A000200033Q001260000300043Q00122Q000400056Q000500016Q0004000200024Q0003000300044Q000200020001001229000200063Q00202Q00020002000700122Q000300086Q00020002000100046Q00012Q006A3Q00023Q00306F3Q0009000A2Q001E3Q00013Q00013Q000E3Q0003043Q007461736B03043Q007761697403133Q004175746F52656672657368496E74657276616C03073Q00456E61626C6564030C3Q0050656E64696E675175657565026Q00084003043Q007761726E03213Q005B4650535D204175746F207265667265736820736B692Q70656420286275737929030B3Q004C6173745265667265736803023Q006F7303053Q00636C6F636B030B3Q0046505320422Q6F7374657203163Q004175746F207265667265736820636F6D706C65746564027Q004000263Q0012183Q00013Q00206Q00024Q00015Q00202Q0001000100036Q000200019Q0000206Q000400064Q000A000100010004503Q000A00012Q001E3Q00014Q006A3Q00014Q0074000100023Q00202Q0001000100056Q000200016Q00033Q00122Q000100068Q0002000200064Q0017000100010004503Q0017000100121A000100073Q001208000200084Q00240001000200012Q001E3Q00014Q006A000100044Q00540001000100014Q000100056Q0001000100014Q000100023Q00122Q0002000A3Q00202Q00020002000B4Q00020001000200102Q0001000900024Q000100063Q00122Q0002000C3Q00122Q0003000D3Q00122Q0004000E6Q0001000400016Q00017Q00053Q00030D3Q005265667265736854687265616403053Q007063612Q6C03043Q007461736B03063Q0063616E63656C2Q000D4Q006A7Q0020235Q00010006073Q000C00013Q0004503Q000C000100121A3Q00023Q001240000100033Q00202Q0001000100044Q00025Q00202Q0002000200016Q000200019Q0000304Q000100052Q001E3Q00017Q00153Q0003073Q00456E61626C65642Q01030C3Q0050656E64696E675175657565030C3Q00497350726F63652Q73696E67010003133Q00497350656E64696E6750726F63652Q73696E67030B3Q004C6173745265667265736803023Q006F7303053Q00636C6F636B030E3Q004D61696E436F2Q6E656374696F6E03053Q007063612Q6C0003173Q00436F2Q6E6563742044657363656E64616E74412Q64656403043Q006D61746803053Q00666C2Q6F7203133Q004175746F52656672657368496E74657276616C026Q004E40030B3Q0046505320422Q6F7374657203273Q00556C74726120537461626C65204D6F646520286175746F2072656672657368207365746961702003073Q00206D656E697429026Q001440003E4Q006A7Q0020235Q00010006073Q000500013Q0004503Q000500012Q001E3Q00014Q006A7Q00307A3Q000100026Q00016Q000100023Q00202Q0001000100036Q000200016Q00023Q00304Q000400056Q00023Q00304Q000600056Q00023Q00122Q000100083Q00202Q0001000100094Q00010001000200104Q000700016Q00038Q000100016Q00048Q000100016Q00023Q00206Q000A00064Q002200013Q0004503Q0022000100121A3Q000B3Q00067800013Q000100012Q006A3Q00024Q00243Q000200012Q006A3Q00023Q00306F3Q000A000C2Q006A3Q00053Q0012080001000D3Q00067800020001000100032Q006A3Q00024Q006A3Q00064Q006A3Q00074Q00533Q000200016Q00088Q000100016Q00098Q000100016Q000A8Q0001000100124Q000E3Q00206Q000F4Q00015Q00202Q00010001001000202Q0001000100116Q000200024Q0001000B3Q00122Q000200123Q00122Q000300136Q00045Q00122Q000500146Q00030003000500122Q000400156Q0001000400016Q00013Q00023Q00023Q00030E3Q004D61696E436F2Q6E656374696F6E030A3Q00446973636F2Q6E65637400054Q00107Q00206Q000100206Q00026Q000200016Q00017Q00033Q00030E3Q004D61696E436F2Q6E656374696F6E030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637400084Q00279Q00000100013Q00202Q00010001000200202Q0001000100034Q000300026Q00010003000200104Q000100016Q00017Q000B3Q0003073Q00456E61626C65640100030E3Q004D61696E436F2Q6E656374696F6E03053Q007063612Q6C00030C3Q0050656E64696E675175657565030C3Q00497350726F63652Q73696E6703133Q00497350656E64696E6750726F63652Q73696E67030B3Q0046505320422Q6F7374657203273Q0044697361626C6564202872656A6F696E20756E74756B20726573746F72652076697375616C7329026Q00104000254Q006A7Q0020235Q00010006623Q0005000100010004503Q000500012Q001E3Q00014Q006A7Q0030473Q000100026Q00018Q000100016Q00028Q000100016Q00038Q000100016Q00043Q00206Q000300064Q001700013Q0004503Q0017000100121A3Q00043Q00067800013Q000100012Q006A3Q00044Q00243Q000200012Q006A3Q00043Q00306F3Q000300052Q006A3Q00054Q0061000100043Q00202Q0001000100066Q000200016Q00043Q00304Q000700026Q00043Q00304Q000800026Q00063Q00122Q000100093Q00122Q0002000A3Q00122Q0003000B8Q000300016Q00013Q00013Q00023Q00030E3Q004D61696E436F2Q6E656374696F6E030A3Q00446973636F2Q6E65637400054Q00107Q00206Q000100206Q00026Q000200016Q00017Q00013Q0003123Q00546F2Q676C652046505320422Q6F7374657201094Q006A00015Q001208000200013Q00067800033Q000100042Q006A3Q00014Q001F8Q006A3Q00024Q006A3Q00034Q00650001000300012Q001E3Q00013Q00013Q00013Q00030B3Q004973526573652Q74696E67000E4Q006A7Q0020235Q00010006073Q000500013Q0004503Q000500012Q001E3Q00014Q006A3Q00013Q0006073Q000B00013Q0004503Q000B00012Q006A3Q00024Q004F3Q000100010004503Q000D00012Q006A3Q00034Q004F3Q000100012Q001E3Q00017Q00013Q0003143Q00546F2Q676C65204E6F74696669636174696F6E7301074Q006A00015Q001208000200013Q00067800033Q000100022Q006A3Q00014Q001F8Q00650001000300012Q001E3Q00013Q00013Q00013Q00030A3Q004D7574654E6F7469667900054Q006C9Q00000100016Q000100013Q00104Q000100016Q00017Q00013Q00030E3Q005365742042617463682053697A6501074Q006A00015Q001208000200013Q00067800033Q000100022Q006A3Q00014Q001F8Q00650001000300012Q001E3Q00013Q00013Q00013Q0003093Q00426174636853697A6500044Q006A8Q006A000100013Q0010433Q000100012Q001E3Q00017Q00013Q0003123Q0053657420436865636B20496E74657276616C01074Q006A00015Q001208000200013Q00067800033Q000100022Q006A3Q00014Q001F8Q00650001000300012Q001E3Q00013Q00013Q00013Q00030D3Q00436865636B496E74657276616C00044Q006A8Q006A000100013Q0010433Q000100012Q001E3Q00017Q00013Q0003143Q0053657420436C65616E757020496E74657276616C01074Q006A00015Q001208000200013Q00067800033Q000100022Q006A3Q00014Q001F8Q00650001000300012Q001E3Q00013Q00013Q00013Q00030F3Q00436C65616E7570496E74657276616C00044Q006A8Q006A000100013Q0010433Q000100012Q001E3Q00017Q00013Q0003113Q00536574204D617820506572204672616D6501074Q006A00015Q001208000200013Q00067800033Q000100022Q006A3Q00014Q001F8Q00650001000300012Q001E3Q00013Q00013Q00013Q0003123Q004D617850726F63652Q735065724672616D6500044Q006A8Q006A000100013Q0010433Q000100012Q001E3Q00017Q00013Q0003103Q00536574204175746F205265667265736801074Q006A00015Q001208000200013Q00067800033Q000100022Q006A3Q00014Q001F8Q00650001000300012Q001E3Q00013Q00013Q00023Q0003133Q004175746F52656672657368496E74657276616C026Q004E4000054Q00639Q00000100013Q00202Q00010001000200104Q000100016Q00017Q00013Q0003133Q00546F2Q676C6520506F737420452Q666563747301084Q006A00015Q001208000200013Q00067800033Q000100032Q006A3Q00014Q001F8Q006A3Q00024Q00650001000300012Q001E3Q00013Q00013Q00023Q00030D3Q0044697361626C65506F7374465803073Q00456E61626C6564000A4Q00799Q00000100013Q00104Q000100019Q0000206Q000200064Q000900013Q0004503Q000900012Q006A3Q00024Q004F3Q000100012Q001E3Q00017Q00013Q00030E3Q00546F2Q676C6520536861646F777301084Q006A00015Q001208000200013Q00067800033Q000100032Q006A3Q00014Q001F8Q006A3Q00024Q00650001000300012Q001E3Q00013Q00013Q00023Q00030E3Q0044697361626C65536861646F777303073Q00456E61626C6564000A4Q00799Q00000100013Q00104Q000100019Q0000206Q000200064Q000900013Q0004503Q000900012Q006A3Q00024Q004F3Q000100012Q001E3Q00017Q00013Q00030D3Q00466F72636520436C65616E757000084Q006A7Q001208000100013Q00067800023Q000100032Q006A3Q00014Q006A3Q00024Q006A3Q00034Q00653Q000200012Q001E3Q00013Q00013Q00043Q00030C3Q0050656E64696E675175657565030B3Q0046505320422Q6F7374657203123Q004D656D6F72792064696265727369686B616E027Q0040000A4Q00779Q00000100013Q00202Q0001000100016Q000200016Q00023Q00122Q000100023Q00122Q000200033Q00122Q000300048Q000300016Q00017Q00013Q00030E3Q0052756E2046752Q6C2053772Q657000084Q006A7Q001208000100013Q00067800023Q000100032Q006A3Q00014Q006A3Q00024Q006A3Q00034Q00653Q000200012Q001E3Q00013Q00013Q00063Q00030C3Q00497350726F63652Q73696E67030B3Q0046505320422Q6F7374657203183Q0053772Q657020736564616E67206265726A616C616E3Q2E027Q004003123Q0046752Q6C2073772Q65702064696D756C6169026Q00084000124Q006A7Q0020235Q00010006073Q000A00013Q0004503Q000A00012Q006A3Q00013Q001233000100023Q00122Q000200033Q00122Q000300048Q000300016Q00014Q006A3Q00024Q00573Q000100016Q00013Q00122Q000100023Q00122Q000200053Q00122Q000300068Q000300016Q00017Q00043Q00030B3Q004973526573652Q74696E672Q0103053Q007063612Q6C012Q00124Q006A7Q00306F3Q000100022Q006A3Q00013Q0006073Q000800013Q0004503Q000800012Q006A3Q00024Q004F3Q000100010004503Q000A00012Q006A3Q00034Q004F3Q0001000100121A3Q00033Q00067800013Q000100022Q006A3Q00044Q006A3Q00014Q00243Q000200012Q006A7Q00306F3Q000100042Q001E3Q00013Q00013Q00013Q002Q033Q0053657400054Q003F7Q00206Q00014Q000200018Q000200016Q00017Q00043Q0003023Q005F4703053Q00466F72676503053Q00465053554903053Q00526573657400153Q00121A3Q00013Q0020235Q00020006073Q001400013Q0004503Q0014000100121A3Q00013Q0020235Q00020020235Q00030006073Q001400013Q0004503Q0014000100121A3Q00013Q0020235Q00020020235Q00030020235Q00040006073Q001400013Q0004503Q0014000100121A3Q00013Q0020235Q00020020235Q00030020235Q00042Q004F3Q000100012Q001E3Q00017Q00", GetFEnv(), ...);
